#include <iostream>
#include <fstream>

#include "out/MathLexer.h"
#include "out/MathParser.h"

using namespace antlr4;

int main(int argc, const char* argv[]) {
  std::ifstream stream;
  stream.open(argv[1]);

  ANTLRInputStream input(stream);
  MathLexer lexer(&input);
  CommonTokenStream tokens(&lexer);
  MathParser parser(&tokens); 

}

