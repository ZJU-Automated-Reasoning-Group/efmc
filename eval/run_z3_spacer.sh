SOLVER="${Z3_ROOT}/bin/z3"
OPTIONS="fp.engine=spacer"
BENCHMARK_DIR=$1
TIMEOUT=$2

#echo "Benchmark dir is ${BENCHMARK_DIR}"
#echo "Timeout is ${TIMEOUT}"

category=`basename ${BENCHMARK_DIR}`
OUTPUT_DIR="${OUTPUT_ROOT}/${category}/z3_spacer"
mkdir -p ${OUTPUT_DIR}

#echo "Output dir is ${OUTPUT_DIR}"
echo "Running Z3_Spacer"

for file in ${BENCHMARK_DIR}/*.smt2; do
    echo ${file}
    filename=`basename ${file}`
    timeout ${TIMEOUT} /usr/bin/time -f'user: %U wall: %e CPU: %PCPU' ${SOLVER} ${OPTIONS} ${file} > ${OUTPUT_DIR}/${filename}.out 2>&1
done