#!/bin/bash

# Generate Makefile from _CoqProject
coq_makefile -f _CoqProject -o Makefile

# Build the project using the generated Makefile
make
