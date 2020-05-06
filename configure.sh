#!/bin/sh

echo "Generating Makefile..." ;
coq_makefile -f _CoqProject -o Makefile ;
echo "Compiling *.v files..." ;
make all;
echo "Compilation completed"