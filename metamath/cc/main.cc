#include <iostream>
#include <fstream>

#include "antlr4-runtime.h"
#include "out/MathLexer.h"
#include "out/MathParser.h"
#include "out/MathBaseListener.h"

using namespace antlr4;

/*class TreeShapeListener : public MathBaseListener {
public:
  void enterStart(ParserRuleContext *ctx) override {
    printf("here\n");
  }
};*/

int main(int argc, const char* argv[]) {
  std::ifstream stream;
  stream.open(argv[1]);

  ANTLRInputStream input(stream);
  MathLexer lexer(&input);
  CommonTokenStream tokens(&lexer);
  MathParser parser(&tokens); 

  tree::ParseTree *tree = parser.start();
  std::cout << tree->toStringTree() << std::endl;
}

