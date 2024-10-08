#for testing
SOLVER="$(pwd)/venv/bin/python3"
#OPTIONS="prover.py --engine efsmt --template power_bv_interval --aux-inv false --lang chc --file"
OPTIONS="prover.py --engine pdr --aux-inv false --lang sygus --file"
BENCHMARK_DIR=$1
TIMEOUT=$2

echo "Benchmark dir is ${BENCHMARK_DIR}"
echo "Timeout is ${TIMEOUT}"

echo "Running kind"

trap "exit" INT
for file in ${BENCHMARK_DIR}/*.sl; do
    echo "Solving ${file}"
    filename=`basename ${file}`
    gtimeout ${TIMEOUT} /usr/bin/time ${SOLVER} ${OPTIONS} ${file}
done
