#BENCHMARK_DIR=$1
#TIMEOUT=$2

script_dir=$(cd "$(dirname "$0")" && pwd)

${script_dir}/run_z3_spacer.sh $1 $2 &
${script_dir}/run_gspacer.sh $1 $2 &
${script_dir}/run_eldarica.sh $1 $2 &
wait
