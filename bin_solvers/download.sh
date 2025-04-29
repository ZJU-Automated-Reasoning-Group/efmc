#!/bin/bash
# This file is used by the Dockerfile outside (for a previous ASE'23 work)
# We may only keep the pysmt-install related commands, so that we can use 
# differnet SMT solvers via the pysmt's Python API.
# And it is not used for now

z3_version=z3-4.10.2-x64-glibc-2.31
pwd
current_dir=$(pwd)

# The following is for pysmt
pysmt-install --msat --confirm-agreement
# install yices2, it takes a long time, comment it if necessary
pysmt-install --yices --confirm-agreement
# install cvc4, it takes a long time, comment it if necessary
pysmt-install --cvc4 --confirm-agreement
# install boolector, it takes a long time, comment it if necessary
pysmt-install --btor --confirm-agreement

# install picosat
pysmt-install --picosat --confirm-agreement

# install bdd
pysmt-install --bdd --confirm-agreement

# Download and build Boolector
git clone https://github.com/boolector/boolector
cd boolector

# Download and build Lingeling
./contrib/setup-lingeling.sh

# Download and build BTOR2Tools
./contrib/setup-btor2tools.sh

# Build Boolector
./configure.sh && cd build && make

eval "cd $current_dir"

# Download and build Bitwuzla
git clone https://github.com/bitwuzla/bitwuzla
cd bitwuzla

# Download and build CaDiCaL
./contrib/setup-cadical.sh

# Download and build BTOR2Tools
./contrib/setup-btor2tools.sh

# Download and build SymFPU
./contrib/setup-symfpu.sh

# Build Bitwuzla
./configure.sh && cd build && make

eval "cd $current_dir"

git clone https://github.com/ltentrup/caqe.git
cd caqe
cargo build --release # may fail , haven't fixed yet
eval "cd $current_dir"


# download eld
wget https://github.com/uuverifiers/eldarica/releases/download/v2.0.9/eldarica-bin-2.0.9.zip


# extract all zip/gz files
eval "find . -maxdepth 1 -type f -name '*.gz' | xargs -I{} tar xvf {}"
eval "find . -maxdepth 1 -type f -name '*.zip' | xargs -I{} unzip {}"

# for installation of q3b
eval "cp $z3_version/bin/libz3.a /usr/lib"
eval "cp $z3_version/include/* /usr/include/"

git clone https://github.com/martinjonas/Q3B.git
cd Q3B
git submodule update --init --recursive # may fail!!!
cmake -B build -DANTLR_EXECUTABLE=/usr/share/java/antlr-4.11.1-complete.jar
cmake --build build -j4
eval "cd $current_dir"



mkdir bin
smt_binaries=("yices-smt2" "bitwuzla" "boolector" "z3" "mathsat" "q3b" "cvc5-Linux" "caqe")
match=""
flag=false
for binary in "${smt_binaries[@]}"
do
  if $flag; then
    match+=" -o -name '$binary'"
  else
    match+=" -name '$binary'"
    flag=true
  fi
  
done


# find smt binaries and cp these files to ./bin
eval "find . -type f \\( $match \\) | xargs -I{} cp {} ./bin/"
eval "find . -maxdepth 1 -type f -name '*.gz' | xargs -I{} rm -f {}"
eval "find . -maxdepth 1 -type f -name '*.zip' | xargs -I{} rm -f {}"
eval "chmod +x ./bin/cvc5-Linux"

eval "ln -s /efmc/bin_solvers/eldarica/eld /efmc/bin_solvers/bin/eld"