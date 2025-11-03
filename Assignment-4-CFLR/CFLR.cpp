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
    pag->dump();

    CFLR solver;
    solver.buildGraph(pag);
    // 完成此方法
    solver.solve();
    solver.dumpResult();

    LLVMModuleSet::releaseLLVMModuleSet();
    return 0;
}


void CFLR::solve()
{
    // 用图中的所有现有边初始化工作表
    for (auto &srcItr : graph->getSuccessorMap())
    {
        unsigned src = srcItr.first;
        for (auto &lblItr : srcItr.second)
        {
            EdgeLabel label = lblItr.first;
            for (auto dst : lblItr.second)
            {
                workList.push(CFLREdge(src, dst, label));
            }
        }
    }

    // 为 VF 和 VA 添加自环边（ε 产生式：VF ::= ε, VA ::= ε）
    // 首先需要获取所有节点
    std::set<unsigned> allNodes;
    for (auto &srcItr : graph->getSuccessorMap())
    {
        allNodes.insert(srcItr.first);
        for (auto &lblItr : srcItr.second)
        {
            for (auto dst : lblItr.second)
            {
                allNodes.insert(dst);
            }
        }
    }
    
    // 添加 VF 和 VA 自环边
    for (unsigned node : allNodes)
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

    // 主要的 CFL-Reachability 算法
    while (!workList.empty())
    {
        CFLREdge edge = workList.pop();
        unsigned src = edge.src;
        unsigned dst = edge.dst;
        EdgeLabel label = edge.label;

        // 根据标签应用语法规则
        switch (label)
        {
            case Addr:
            {
                // PT ::= Addr VF
                // 如果有 Addr: src -> dst，检查是否存在 VF: dst -> x，然后添加 PT: src -> x
                for (auto &vfItr : graph->getSuccessorMap()[dst])
                {
                    if (vfItr.first == VF)
                    {
                        for (auto x : vfItr.second)
                        {
                            if (!graph->hasEdge(src, x, PT))
                            {
                                graph->addEdge(src, x, PT);
                                workList.push(CFLREdge(src, x, PT));
                            }
                        }
                    }
                }
                
                // PT ::= VF Addr
                // 如果有 VF: x -> src，并且 Addr: src -> dst，那么添加 PT: x -> dst
                for (auto &vfItr : graph->getPredecessorMap()[src])
                {
                    if (vfItr.first == VF)
                    {
                        for (auto x : vfItr.second)
                        {
                            if (!graph->hasEdge(x, dst, PT))
                            {
                                graph->addEdge(x, dst, PT);
                                workList.push(CFLREdge(x, dst, PT));
                            }
                        }
                    }
                }
                break;
            }
            
            case Copy:
            {
                // VF ::= Copy
                // 如果有 Copy: src -> dst，添加 VF: src -> dst
                if (!graph->hasEdge(src, dst, VF))
                {
                    graph->addEdge(src, dst, VF);
                    workList.push(CFLREdge(src, dst, VF));
                }
                break;
            }
            
            case Store:
            {
                // SV ::= Store VA
                // 如果有 Store: src -> dst，检查是否存在 VA: dst -> x，然后添加 SV: src -> x
                for (auto &vaItr : graph->getSuccessorMap()[dst])
                {
                    if (vaItr.first == VA)
                    {
                        for (auto x : vaItr.second)
                        {
                            if (!graph->hasEdge(src, x, SV))
                            {
                                graph->addEdge(src, x, SV);
                                workList.push(CFLREdge(src, x, SV));
                            }
                        }
                    }
                }
                
                // SV ::= VA Store
                // 如果有 VA: x -> src，并且 Store: src -> dst，那么添加 SV: x -> dst
                for (auto &vaItr : graph->getPredecessorMap()[src])
                {
                    if (vaItr.first == VA)
                    {
                        for (auto x : vaItr.second)
                        {
                            if (!graph->hasEdge(x, dst, SV))
                            {
                                graph->addEdge(x, dst, SV);
                                workList.push(CFLREdge(x, dst, SV));
                            }
                        }
                    }
                }
                
                // VF ::= Store VP
                // 如果有 Store: src -> dst，检查是否存在 VP: dst -> x，然后添加 VF: src -> x
                for (auto &vpItr : graph->getSuccessorMap()[dst])
                {
                    if (vpItr.first == VP)
                    {
                        for (auto x : vpItr.second)
                        {
                            if (!graph->hasEdge(src, x, VF))
                            {
                                graph->addEdge(src, x, VF);
                                workList.push(CFLREdge(src, x, VF));
                            }
                        }
                    }
                }
                
                // VF ::= PV Store
                // 如果有 PV: x -> src，并且 Store: src -> dst，那么添加 VF: x -> dst
                for (auto &pvItr : graph->getPredecessorMap()[src])
                {
                    if (pvItr.first == PV)
                    {
                        for (auto x : pvItr.second)
                        {
                            if (!graph->hasEdge(x, dst, VF))
                            {
                                graph->addEdge(x, dst, VF);
                                workList.push(CFLREdge(x, dst, VF));
                            }
                        }
                    }
                }
                break;
            }
            
            case Load:
            {
                // LV ::= Load VA
                // 如果有 Load: src -> dst，检查是否存在 VA: dst -> x，然后添加 LV: src -> x
                for (auto &vaItr : graph->getSuccessorMap()[dst])
                {
                    if (vaItr.first == VA)
                    {
                        for (auto x : vaItr.second)
                        {
                            if (!graph->hasEdge(src, x, LV))
                            {
                                graph->addEdge(src, x, LV);
                                workList.push(CFLREdge(src, x, LV));
                            }
                        }
                    }
                }
                
                // VA ::= LV Load
                // 如果有 LV: x -> src，并且 Load: src -> dst，那么添加 VA: x -> dst
                for (auto &lvItr : graph->getPredecessorMap()[src])
                {
                    if (lvItr.first == LV)
                    {
                        for (auto x : lvItr.second)
                        {
                            if (!graph->hasEdge(x, dst, VA))
                            {
                                graph->addEdge(x, dst, VA);
                                workList.push(CFLREdge(x, dst, VA));
                            }
                        }
                    }
                }
                
                // VF ::= SV Load
                // 如果有 SV: x -> src，并且 Load: src -> dst，那么添加 VF: x -> dst
                for (auto &svItr : graph->getPredecessorMap()[src])
                {
                    if (svItr.first == SV)
                    {
                        for (auto x : svItr.second)
                        {
                            if (!graph->hasEdge(x, dst, VF))
                            {
                                graph->addEdge(x, dst, VF);
                                workList.push(CFLREdge(x, dst, VF));
                            }
                        }
                    }
                }
                
                // VF ::= PV Load
                // 如果有 PV: x -> src，并且 Load: src -> dst，那么添加 VF: x -> dst
                for (auto &pvItr : graph->getPredecessorMap()[src])
                {
                    if (pvItr.first == PV)
                    {
                        for (auto x : pvItr.second)
                        {
                            if (!graph->hasEdge(x, dst, VF))
                            {
                                graph->addEdge(x, dst, VF);
                                workList.push(CFLREdge(x, dst, VF));
                            }
                        }
                    }
                }
                
                // VF ::= Load SV
                // 如果有 Load: src -> dst，检查是否存在 SV: dst -> x，然后添加 VF: src -> x
                for (auto &svItr : graph->getSuccessorMap()[dst])
                {
                    if (svItr.first == SV)
                    {
                        for (auto x : svItr.second)
                        {
                            if (!graph->hasEdge(src, x, VF))
                            {
                                graph->addEdge(src, x, VF);
                                workList.push(CFLREdge(src, x, VF));
                            }
                        }
                    }
                }
                
                // VF ::= Load VP
                // 如果有 Load: src -> dst，检查是否存在 VP: dst -> x，然后添加 VF: src -> x
                for (auto &vpItr : graph->getSuccessorMap()[dst])
                {
                    if (vpItr.first == VP)
                    {
                        for (auto x : vpItr.second)
                        {
                            if (!graph->hasEdge(src, x, VF))
                            {
                                graph->addEdge(src, x, VF);
                                workList.push(CFLREdge(src, x, VF));
                            }
                        }
                    }
                }
                break;
            }
            
            case VF:
            {
                // VF ::= VF VF
                // 如果有 VF: src -> dst，检查是否存在 VF: dst -> x，然后添加 VF: src -> x
                for (auto &vfItr : graph->getSuccessorMap()[dst])
                {
                    if (vfItr.first == VF)
                    {
                        for (auto x : vfItr.second)
                        {
                            if (!graph->hasEdge(src, x, VF))
                            {
                                graph->addEdge(src, x, VF);
                                workList.push(CFLREdge(src, x, VF));
                            }
                        }
                    }
                }
                
                // VF ::= VF VF (左侧)
                // 如果有 VF: x -> src，并且 VF: src -> dst，那么添加 VF: x -> dst
                for (auto &vfItr : graph->getPredecessorMap()[src])
                {
                    if (vfItr.first == VF)
                    {
                        for (auto x : vfItr.second)
                        {
                            if (!graph->hasEdge(x, dst, VF))
                            {
                                graph->addEdge(x, dst, VF);
                                workList.push(CFLREdge(x, dst, VF));
                            }
                        }
                    }
                }
                break;
            }
            
            case VA:
            {
                // VA ::= VF VA
                // 如果有 VF: src -> dst，检查是否存在 VA: dst -> x，然后添加 VA: src -> x
                for (auto &vaItr : graph->getSuccessorMap()[dst])
                {
                    if (vaItr.first == VA)
                    {
                        for (auto x : vaItr.second)
                        {
                            if (!graph->hasEdge(src, x, VA))
                            {
                                graph->addEdge(src, x, VA);
                                workList.push(CFLREdge(src, x, VA));
                            }
                        }
                    }
                }
                
                // VA ::= VA VF
                // 如果有 VA: x -> src，并且 VF: src -> dst，那么添加 VA: x -> dst
                for (auto &vaItr : graph->getPredecessorMap()[src])
                {
                    if (vaItr.first == VA)
                    {
                        for (auto x : vaItr.second)
                        {
                            if (!graph->hasEdge(x, dst, VA))
                            {
                                graph->addEdge(x, dst, VA);
                                workList.push(CFLREdge(x, dst, VA));
                            }
                        }
                    }
                }
                break;
            }
            
            case SV:
            {
                // VF ::= SV Load
                // 如果有 SV: src -> dst，检查是否存在 Load: dst -> x，然后添加 VF: src -> x
                for (auto &loadItr : graph->getSuccessorMap()[dst])
                {
                    if (loadItr.first == Load)
                    {
                        for (auto x : loadItr.second)
                        {
                            if (!graph->hasEdge(src, x, VF))
                            {
                                graph->addEdge(src, x, VF);
                                workList.push(CFLREdge(src, x, VF));
                            }
                        }
                    }
                }
                break;
            }
            
            case PV:
            {
                // PV ::= PT VA
                // 如果有 PT: src -> dst，检查是否存在 VA: dst -> x，然后添加 PV: src -> x
                for (auto &vaItr : graph->getSuccessorMap()[dst])
                {
                    if (vaItr.first == VA)
                    {
                        for (auto x : vaItr.second)
                        {
                            if (!graph->hasEdge(src, x, PV))
                            {
                                graph->addEdge(src, x, PV);
                                workList.push(CFLREdge(src, x, PV));
                            }
                        }
                    }
                }
                
                // VF ::= PV Load
                // 如果有 PV: src -> dst，检查是否存在 Load: dst -> x，然后添加 VF: src -> x
                for (auto &loadItr : graph->getSuccessorMap()[dst])
                {
                    if (loadItr.first == Load)
                    {
                        for (auto x : loadItr.second)
                        {
                            if (!graph->hasEdge(src, x, VF))
                            {
                                graph->addEdge(src, x, VF);
                                workList.push(CFLREdge(src, x, VF));
                            }
                        }
                    }
                }
                break;
            }
            
            case VP:
            {
                // VP ::= VA PT
                // 如果有 VA: x -> src，并且 PT: src -> dst，那么添加 VP: x -> dst
                for (auto &vaItr : graph->getPredecessorMap()[src])
                {
                    if (vaItr.first == VA)
                    {
                        for (auto x : vaItr.second)
                        {
                            if (!graph->hasEdge(x, dst, VP))
                            {
                                graph->addEdge(x, dst, VP);
                                workList.push(CFLREdge(x, dst, VP));
                            }
                        }
                    }
                }
                
                // VF ::= Store VP
                // 如果有 Store: x -> src，并且 VP: src -> dst，那么添加 VF: x -> dst
                for (auto &storeItr : graph->getPredecessorMap()[src])
                {
                    if (storeItr.first == Store)
                    {
                        for (auto x : storeItr.second)
                        {
                            if (!graph->hasEdge(x, dst, VF))
                            {
                                graph->addEdge(x, dst, VF);
                                workList.push(CFLREdge(x, dst, VF));
                            }
                        }
                    }
                }
                break;
            }
            
            case LV:
            {
                // LV 可用于 VA ::= LV Load
                // 此情况处理当 LV 边被添加时
                break;
            }
            
            case PT:
            {
                // PT ::= VF Addr (在 Addr 情况中处理)
                // PT ::= Addr VF (在 Addr 情况中处理)
                // PT 可用于 PV ::= PT VA 和 VP ::= VA PT
                // PV ::= PT VA
                // 如果有 PT: src -> dst，检查是否存在 VA: dst -> x，然后添加 PV: src -> x
                for (auto &vaItr : graph->getSuccessorMap()[dst])
                {
                    if (vaItr.first == VA)
                    {
                        for (auto x : vaItr.second)
                        {
                            if (!graph->hasEdge(src, x, PV))
                            {
                                graph->addEdge(src, x, PV);
                                workList.push(CFLREdge(src, x, PV));
                            }
                        }
                    }
                }
                
                // VP ::= VA PT
                // 如果有 VA: x -> src，并且 PT: src -> dst，那么添加 VP: x -> dst
                for (auto &vaItr : graph->getPredecessorMap()[src])
                {
                    if (vaItr.first == VA)
                    {
                        for (auto x : vaItr.second)
                        {
                            if (!graph->hasEdge(x, dst, VP))
                            {
                                graph->addEdge(x, dst, VP);
                                workList.push(CFLREdge(x, dst, VP));
                            }
                        }
                    }
                }
                break;
            }
            
            default:
                break;
        }
    }
}
