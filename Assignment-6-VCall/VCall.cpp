/**
 * Andersen.cpp
 * @author kisslune
 */

#include "A6Header.h"
#include "Graphs/ConsG.h"
#include "Graphs/ConsGNode.h"
#include "Graphs/ConsGEdge.h"
#include "Util/SVFUtil.h"
#include "Util/WorkList.h"

using namespace llvm;
using namespace std;
using namespace SVF;


int main(int argc, char** argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    SVF::LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVF::SVFIRBuilder builder;
    auto pag = builder.build();
    auto consg = new SVF::ConstraintGraph(pag);
    consg->dump();

    Andersen andersen(consg);
    auto cg = pag->getCallGraph();

    // TODO: complete the following two methods
    andersen.runPointerAnalysis();
    andersen.updateCallGraph(cg);

    cg->dump();
    SVF::LLVMModuleSet::releaseLLVMModuleSet();
	return 0;
}


void Andersen::runPointerAnalysis()
{
    // TODO: complete this method. Point-to set and worklist are defined in A5Header.h
    //  The implementation of constraint graph is provided in the SVF library
        // TODO: complete this method. Point-to set and worklist are defined in A5Header.h
    //  The implementation of constraint graph is provided in the SVF library
    WorkList<NodeID> workList;

    // ==========================================
    // 1. Address Rule (Initialization)
    // ==========================================
    // Pseudocode: for each o --Address--> p
    for (auto it = consg->begin(); it != consg->end(); ++it)
    {
        ConstraintNode* node = it->second;
        NodeID o = node->getId(); // node represents object o

        for (auto edge : node->getAddrOutEdges())
        {
            auto addrEdge = SVFUtil::dyn_cast<AddrCGEdge>(edge);
            if (!addrEdge) continue;

            NodeID p = addrEdge->getDstID(); // destination pointer p

            // pts(p) = {o}
            if (pts[p].insert(o).second)
            {
                workList.push(p);
            }
        }
    }

    // ==========================================
    // 2. Propagation (Main Worklist Loop)
    // ==========================================
    while (!workList.empty())
    {
        NodeID p = workList.pop();
        ConstraintNode* nodeP = consg->getGNode(p);
        if (!nodeP) continue;

        // -------------------------------------------------------
        // Store Rule: *p = q   (q --Store--> p)
        // -------------------------------------------------------
        for (auto edge : nodeP->getInEdges())
        {
            auto storeEdge = SVFUtil::dyn_cast<StoreCGEdge>(edge);
            if (!storeEdge) continue;

            NodeID q = storeEdge->getSrcID();

            for (auto o : pts[p])
            {
                ConstraintNode* qNode = consg->getGNode(q);
                ConstraintNode* oNode = consg->getGNode(o);

                // Add q -> o as Copy edge if not exist
                if (!consg->hasEdge(qNode, oNode, ConstraintEdge::Copy))
                {
                    consg->addCopyCGEdge(q, o);
                    workList.push(q);
                }
            }
        }

        // -------------------------------------------------------
        // Load Rule: r = *p   (p --Load--> r)
        // -------------------------------------------------------
        for (auto edge : nodeP->getLoadOutEdges())
        {
            auto loadEdge = SVFUtil::dyn_cast<LoadCGEdge>(edge);
            if (!loadEdge) continue;

            NodeID r = loadEdge->getDstID();

            for (auto o : pts[p])
            {
                ConstraintNode* oNode = consg->getGNode(o);
                ConstraintNode* rNode = consg->getGNode(r);

                // Add o -> r as Copy edge if not exist
                if (!consg->hasEdge(oNode, rNode, ConstraintEdge::Copy))
                {
                    consg->addCopyCGEdge(o, r);
                    workList.push(o);
                }
            }
        }

        // -------------------------------------------------------
        // Copy Rule: x = p   (p --Copy--> x)
        // -------------------------------------------------------
        for (auto edge : nodeP->getCopyOutEdges())
        {
            auto copyEdge = SVFUtil::dyn_cast<CopyCGEdge>(edge);
            if (!copyEdge) continue;

            NodeID x = copyEdge->getDstID();

            size_t oldSize = pts[x].size();
            pts[x].insert(pts[p].begin(), pts[p].end());

            if (pts[x].size() != oldSize)
            {
                workList.push(x);
            }
        }

        // -------------------------------------------------------
        // Gep Rule: x = gep(p, offset)
        // -------------------------------------------------------
        for (auto edge : nodeP->getGepOutEdges())
        {
            NodeID x = edge->getDstID();
            u32_t offset = 0;   // default field offset
            bool isGep = false;

            // Case 1: Constant offset (e.g., struct field, array[0])
            if (auto normalGep = SVFUtil::dyn_cast<NormalGepCGEdge>(edge))
            {
                offset = normalGep->getConstantFieldIdx();
                isGep = true;
            }
            // Case 2: Variant offset (e.g., array[i])
            else if (auto variantGep = SVFUtil::dyn_cast<VariantGepCGEdge>(edge))
            {
                // API limitation: cannot extract real offset, fallback to 0
                // Interpretation: p must already point to correct array base
                offset = 0;
                isGep = true;
            }

            if (!isGep) continue;

            size_t oldSize = pts[x].size();

            for (auto o : pts[p])
            {
                // For constant offset: fld = o.field
                // For variant offset: fld = o (base object)
                NodeID fld = consg->getGepObjVar(o, offset);
                pts[x].insert(fld);
            }

            if (pts[x].size() != oldSize)
            {
                workList.push(x);
            }
        }
    }
}

void Andersen::updateCallGraph(SVF::CallGraph* cg)
{
    // TODO: complete this method.
    //  The implementation of call graph is provided in the SVF library
    // 1. 获取所有间接调用点
    const auto& indirectCalls = consg->getIndirectCallsites();

    for (auto &entry : indirectCalls)
    {
        const CallICFGNode* cs = entry.first;   // 调用点
        NodeID funcPtrNodeID = entry.second;    // 对应函数指针节点

        // 获取调用点所在函数
        const FunObjVar* callerFun = cs->getCaller();
        if (!callerFun) continue;

        // 查找指针分析结果
        auto itPts = pts.find(funcPtrNodeID);
        if (itPts == pts.end()) continue;

        const std::set<NodeID>& targets = itPts->second;

        // 遍历可能指向的函数节点
        for (NodeID targetID : targets)
        {
            if (!consg->isFunction(targetID)) continue;

            const FunObjVar* calleeFun = consg->getFunction(targetID);
            if (!calleeFun) continue;

            // 将间接调用边加入调用图
            cg->addIndirectCallGraphEdge(cs, callerFun, calleeFun);
        }
    }
}
