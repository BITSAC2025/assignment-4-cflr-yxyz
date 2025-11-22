/**
 * SVFIR.cpp
 * @author kisslune
 */

#include "Graphs/SVFG.h"
#include "SVF-LLVM/SVFIRBuilder.h"

using namespace SVF;
using namespace llvm;
using namespace std;

int main(int argc, char** argv)
{
    int arg_num = 0;
    int extraArgc = 4;
    char** arg_value = new char*[argc + extraArgc];
    for (; arg_num < argc; ++arg_num) {
        arg_value[arg_num] = argv[arg_num];
    }
    std::vector<std::string> moduleNameVec;

    int orgArgNum = arg_num;
    arg_value[arg_num++] = (char*)"-model-arrays=true";
    arg_value[arg_num++] = (char*)"-pre-field-sensitive=false";
    arg_value[arg_num++] = (char*)"-model-consts=true";
    arg_value[arg_num++] = (char*)"-stat=false";
    assert(arg_num == (orgArgNum + extraArgc) && "more extra arguments? Change the value of extraArgc");

    moduleNameVec = OptionBase::parseOptions(arg_num, arg_value, "SVF IR", "[options] <input-bitcode...>");

    LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(moduleNameVec);

    // Instantiate an SVFIR builder
    SVFIRBuilder builder;
    cout << "Generating SVFIR(PAG), call graph and ICFG ..." << endl;

    // TODO: here, generate SVFIR(PAG), call graph and ICFG, and dump them to files
    //@{
    // 1. 生成SVFIR（即程序赋值图PAG）：SVFIRBuilder::build()返回PAG实例
    auto pag = builder.build();
    
    // 2. 从PAG中获取调用图（CG）和跨过程控制流图（ICFG）：
    const CallGraph* callGraph = pag->getCallGraph();  // 获取函数调用关系图
    ICFG* interCFG = pag->getICFG();                   // 获取跨过程控制流图
    
    // 3. 从输入文件名生成输出文件名前缀
    // 获取第一个输入文件的路径，提取文件名（保留完整文件名）
    string inputFile = moduleNameVec.empty() ? "" : moduleNameVec[0];
    size_t lastSlash = inputFile.find_last_of("/\\");
    string fileName = (lastSlash == string::npos) ? inputFile : inputFile.substr(lastSlash + 1);
    
    // 4. 导出图为Dot文件
    // 注意：dump 方法的参数是文件名前缀，会自动添加 .dot 扩展名
    pag->dump(fileName + ".pag");                      // 导出PAG（程序赋值图），生成 .pag.dot 文件
    const_cast<CallGraph*>(callGraph)->dump(fileName + ".cg");  // 导出CallGraph（调用图），生成 .cg.dot 文件
    interCFG->dump(fileName + ".icfg");                 // 导出ICFG（跨过程控制流图），生成 .icfg.dot 文件
    
    // 5. 释放资源（SVFIR 会管理其内部资源）
    //@}
    delete[] arg_value;

    return 0;
}
