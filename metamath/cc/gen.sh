#!/bin/bash
java -jar ~/Downloads/antlr-4.7.2-complete.jar -o out -Dlanguage=Cpp Math.g
scons

clang++ -std=c++11 -I /usr/local/Cellar/antlr4-cpp-runtime/4.7.2/include/antlr4-runtime main.cc out/*.cpp -lantlr4-runtime

