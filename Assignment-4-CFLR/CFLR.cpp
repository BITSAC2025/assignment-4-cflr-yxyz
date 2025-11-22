/**
 * CFLR.cpp
 * @author kisslune 
 */

#include "A4Header.h"

using namespace SVF;
using namespace llvm;
using namespace std;

int main(int argc, char **argv)
{
    auto moduleNameVec =
            OptionBase::parseOptions(argc, argv, "Whole Program Points-to Analysis",
                                     "[options] <input-bitcode...>");

    LLVMModuleSet::buildSVFModule(moduleNameVec);

    SVFIRBuilder builder;
    auto pag = builder.build();
    std::string pagDotFile = pag->getModuleIdentifier() + ".dot";
    pag->dump(pagDotFile);

    CFLR solver;
    solver.buildGraph(pag);
    // TODO: complete this method
    solver.solve();
    solver.dumpResult();

    LLVMModuleSet::releaseLLVMModuleSet();
    return 0;
}


void CFLR::solve()
{
    if (!graph)
        return;
    
    // Initialize VF and VA as reflexive (VF ∷= ε, VA ∷= ε)
    // Collect all nodes first
    std::set<unsigned> allNodes;
    auto &succMap = graph->getSuccessorMap();
    auto &predMap = graph->getPredecessorMap();
    
    for (auto &nodeItr : succMap)
    {
        allNodes.insert(nodeItr.first);
        for (auto &lblItr : nodeItr.second)
        {
            for (auto dst : lblItr.second)
            {
                allNodes.insert(dst);
            }
        }
    }
    for (auto &nodeItr : predMap)
    {
        allNodes.insert(nodeItr.first);
        for (auto &lblItr : nodeItr.second)
        {
            for (auto src : lblItr.second)
            {
                allNodes.insert(src);
            }
        }
    }
    
    // Add reflexive edges for VF and VA
    for (auto node : allNodes)
    {
        if (!graph->hasEdge(node, node, VF))
        {
            graph->addEdge(node, node, VF);
            workList.push(CFLREdge(node, node, VF));
        }
        if (!graph->hasEdge(node, node, VA))
        {
            graph->addEdge(node, node, VA);
            workList.push(CFLREdge(node, node, VA));
        }
    }
    
    // Initialize worklist with all existing edges (Addr, Copy, Store, Load)
    for (auto &nodeItr : succMap)
    {
        unsigned src = nodeItr.first;
        for (auto &lblItr : nodeItr.second)
        {
            EdgeLabel label = lblItr.first;
            // Add initial edges (Addr, Copy, Store, Load) to worklist
            if (label == Addr || label == Copy || label == Store || label == Load)
            {
                for (auto dst : lblItr.second)
                {
                    workList.push(CFLREdge(src, dst, label));
                }
            }
        }
    }

    // Main algorithm: process worklist until empty
    while (!workList.empty())
    {
        CFLREdge edge = workList.pop();
        unsigned u = edge.src;
        unsigned v = edge.dst;
        EdgeLabel label = edge.label;

        // Helper function to add edge if not exists
        auto addNewEdge = [this](unsigned src, unsigned dst, EdgeLabel lbl) {
            if (!graph->hasEdge(src, dst, lbl))
            {
                graph->addEdge(src, dst, lbl);
                workList.push(CFLREdge(src, dst, lbl));
            }
        };

        // Get fresh references to maps in each iteration to avoid stale references
        auto &succMap = graph->getSuccessorMap();
        auto &predMap = graph->getPredecessorMap();

        // Apply grammar rules based on the current edge label
        switch (label)
        {
            // Rule: PT ∷= VF Addr
            case VF:
            {
                // VF is reflexive (already initialized)
                // Rule: PT ∷= VF Addr (if u --VF--> v and v --Addr--> w, then u --PT--> w)
                if (succMap.find(v) != succMap.end() && succMap[v].find(Addr) != succMap[v].end())
                {
                    for (auto w : succMap[v][Addr])
                    {
                        addNewEdge(u, w, PT);
                    }
                }
                // Rule: PT ∷= Addr VF (reverse: if prev --Addr--> u and u --VF--> v, then prev --PT--> v)
                if (predMap.find(u) != predMap.end() && predMap[u].find(Addr) != predMap[u].end())
                {
                    for (auto prev : predMap[u][Addr])
                    {
                        addNewEdge(prev, v, PT);
                    }
                }
                // Rule: VF ∷= VF VF (if u --VF--> v and v --VF--> w, then u --VF--> w)
                if (succMap.find(v) != succMap.end() && succMap[v].find(VF) != succMap[v].end())
                {
                    for (auto w : succMap[v][VF])
                    {
                        addNewEdge(u, w, VF);
                    }
                }
                // Rule: VA ∷= VF VA (if u --VF--> v and v --VA--> w, then u --VA--> w)
                if (succMap.find(v) != succMap.end() && succMap[v].find(VA) != succMap[v].end())
                {
                    for (auto w : succMap[v][VA])
                    {
                        addNewEdge(u, w, VA);
                    }
                }
                // Rule: VA ∷= VA VF (if prev --VA--> u and u --VF--> v, then prev --VA--> v)
                if (predMap.find(u) != predMap.end() && predMap[u].find(VA) != predMap[u].end())
                {
                    for (auto prev : predMap[u][VA])
                    {
                        addNewEdge(prev, v, VA);
                    }
                }
                break;
            }

            // Rule: PT ∷= Addr VF
            case Addr:
            {
                // Rule: PT ∷= Addr VF (if u --Addr--> v and v --VF--> w, then u --PT--> w)
                if (succMap.find(v) != succMap.end() && succMap[v].find(VF) != succMap[v].end())
                {
                    for (auto w : succMap[v][VF])
                    {
                        addNewEdge(u, w, PT);
                    }
                }
                // Rule: PT ∷= VF Addr (reverse: if prev --VF--> u and u --Addr--> v, then prev --PT--> v)
                if (predMap.find(u) != predMap.end() && predMap[u].find(VF) != predMap[u].end())
                {
                    for (auto prev : predMap[u][VF])
                    {
                        addNewEdge(prev, v, PT);
                    }
                }
                break;
            }

            // Rule: VF ∷= Copy
            case Copy:
            {
                // Copy directly becomes VF
                addNewEdge(u, v, VF);
                break;
            }

            // Rule: SV ∷= Store VA, then VF ∷= SV Load
            case Store:
            {
                // Rule: SV ∷= Store VA (if u --Store--> v and v --VA--> w, then u --SV--> w)
                if (succMap.find(v) != succMap.end() && succMap[v].find(VA) != succMap[v].end())
                {
                    for (auto w : succMap[v][VA])
                    {
                        addNewEdge(u, w, SV);
                    }
                }
                // Rule: SV ∷= VA Store (if prev --VA--> u and u --Store--> v, then prev --SV--> v)
                if (predMap.find(u) != predMap.end() && predMap[u].find(VA) != predMap[u].end())
                {
                    for (auto prev : predMap[u][VA])
                    {
                        addNewEdge(prev, v, SV);
                    }
                }
                // Rule: VF ∷= Store VP (if u --Store--> v and v --VP--> w, then u --VF--> w)
                if (succMap.find(v) != succMap.end() && succMap[v].find(VP) != succMap[v].end())
                {
                    for (auto w : succMap[v][VP])
                    {
                        addNewEdge(u, w, VF);
                    }
                }
                break;
            }

            // Rule: LV ∷= Load VA, then VA ∷= LV Load, and VF ∷= SV Load, VF ∷= PV Load
            case Load:
            {
                // Rule: LV ∷= Load VA (if there's VA from v, create LV from u)
                if (succMap.find(v) != succMap.end() && succMap[v].find(VA) != succMap[v].end())
                {
                    for (auto w : succMap[v][VA])
                    {
                        addNewEdge(u, w, LV);
                    }
                }
                // Rule: VA ∷= LV Load (if there's LV to u, create VA from prev to v)
                if (predMap.find(u) != predMap.end() && predMap[u].find(LV) != predMap[u].end())
                {
                    for (auto prev : predMap[u][LV])
                    {
                        addNewEdge(prev, v, VA);
                    }
                }
                // Rule: VF ∷= SV Load (if there's SV to u, create VF from prev to v)
                if (predMap.find(u) != predMap.end() && predMap[u].find(SV) != predMap[u].end())
                {
                    for (auto prev : predMap[u][SV])
                    {
                        addNewEdge(prev, v, VF);
                    }
                }
                // Rule: VF ∷= PV Load (if there's PV to u, create VF from prev to v)
                if (predMap.find(u) != predMap.end() && predMap[u].find(PV) != predMap[u].end())
                {
                    for (auto prev : predMap[u][PV])
                    {
                        addNewEdge(prev, v, VF);
                    }
                }
                break;
            }

            // Rule: SV ∷= Store VA
            case SV:
            {
                // Rule: VF ∷= SV Load (if there's Load from v, create VF from u)
                if (succMap.find(v) != succMap.end() && succMap[v].find(Load) != succMap[v].end())
                {
                    for (auto w : succMap[v][Load])
                    {
                        addNewEdge(u, w, VF);
                    }
                }
                break;
            }

            // Rule: PV ∷= PT VA
            case PV:
            {
                // Rule: VF ∷= PV Load (if there's Load from v, create VF from u)
                if (succMap.find(v) != succMap.end() && succMap[v].find(Load) != succMap[v].end())
                {
                    for (auto w : succMap[v][Load])
                    {
                        addNewEdge(u, w, VF);
                    }
                }
                break;
            }

            // Rule: VP ∷= VA PT
            case VP:
            {
                // Rule: VF ∷= Store VP (if there's Store to u, create VF from prev to v)
                if (predMap.find(u) != predMap.end() && predMap[u].find(Store) != predMap[u].end())
                {
                    for (auto prev : predMap[u][Store])
                    {
                        addNewEdge(prev, v, VF);
                    }
                }
                break;
            }

            // Rule: VA ∷= LV Load
            case LV:
            {
                // Rule: VA ∷= LV Load (if there's Load from v, create VA from u)
                if (succMap.find(v) != succMap.end() && succMap[v].find(Load) != succMap[v].end())
                {
                    for (auto w : succMap[v][Load])
                    {
                        addNewEdge(u, w, VA);
                    }
                }
                break;
            }

            // Rule: VA ∷= ε (reflexive)
            case VA:
            {
                // VA is reflexive (already initialized)
                // Rule: VA ∷= VF VA (already handled in VF case)
                // Rule: VA ∷= VA VF (already handled in VF case)
                // Rule: SV ∷= Store VA (already handled in Store case)
                // Rule: SV ∷= VA Store (already handled in Store case)
                // Rule: PV ∷= PT VA
                if (predMap.find(u) != predMap.end() && predMap[u].find(PT) != predMap[u].end())
                {
                    for (auto prev : predMap[u][PT])
                    {
                        addNewEdge(prev, v, PV);
                    }
                }
                // Rule: VP ∷= VA PT
                if (succMap.find(v) != succMap.end() && succMap[v].find(PT) != succMap[v].end())
                {
                    for (auto w : succMap[v][PT])
                    {
                        addNewEdge(u, w, VP);
                    }
                }
                // Rule: LV ∷= Load VA (already handled in Load case)
                break;
            }

            // Rule: PT ∷= VF Addr, PT ∷= Addr VF
            case PT:
            {
                // Rule: PV ∷= PT VA (if there's VA from v, create PV from u)
                if (succMap.find(v) != succMap.end() && succMap[v].find(VA) != succMap[v].end())
                {
                    for (auto w : succMap[v][VA])
                    {
                        addNewEdge(u, w, PV);
                    }
                }
                // Rule: VP ∷= VA PT (if there's VA to u, create VP from prev to v)
                if (predMap.find(u) != predMap.end() && predMap[u].find(VA) != predMap[u].end())
                {
                    for (auto prev : predMap[u][VA])
                    {
                        addNewEdge(prev, v, VP);
                    }
                }
                break;
            }

            default:
                break;
        }
    }
}
