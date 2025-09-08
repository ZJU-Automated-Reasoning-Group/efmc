"""
LLM4Inv Demo: Guess-and-Check Style Invariant Inference
"""

import logging
import time
import z3
from typing import Dict, Any
import os
import glob

from efmc.sts import TransitionSystem
from efmc.engines.llm4inv.llm4inv_prover import LLM4InvProver
from efmc.frontends.chc_parser import CHCParser

logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)


def create_counter_example() -> TransitionSystem:
    """
    Create a simple counter example with overflow check.
    
    Program: 
    - x starts at 0
    - x increments by 1 while x < 100
    - Safety property: x <= 100
    """
    # Create bit-vector variables
    x = z3.BitVec('x', 32)             
    x_prime = z3.BitVec('x!', 32)
    
    # Initial condition: x == 0
    init = x == z3.BitVecVal(0, 32)
    
    # Transition relation: x' = x + 1 if x < 100, else x' = x
    trans = z3.Or(
        z3.And(z3.ULT(x, z3.BitVecVal(100, 32)), x_prime == x + z3.BitVecVal(1, 32)),
        z3.And(z3.UGE(x, z3.BitVecVal(100, 32)), x_prime == x)
    )
    
    # Safety property: x <= 100
    post = z3.ULE(x, z3.BitVecVal(100, 32))
    
    # Create transition system
    sts = TransitionSystem(
        variables=[x],
        prime_variables=[x_prime],
        init=init,
        trans=trans,
        post=post
    )
    
    return sts


def create_array_bounds_example() -> TransitionSystem:
    """
    Create an array bounds checking example.
    
    Program:
    - i starts at 0
    - i increments while i < n
    - Safety property: i <= n
    """
    i = z3.BitVec('i', 32)
    n = z3.BitVec('n', 32)
    i_prime = z3.BitVec('i!', 32)
    n_prime = z3.BitVec('n!', 32)
    
    # Initial condition: i == 0, n > 0
    init = z3.And(i == z3.BitVecVal(0, 32), z3.UGT(n, z3.BitVecVal(0, 32)))
    
    # Transition relation: i' = i + 1 if i < n, else i' = i; n' = n
    trans = z3.And(
        z3.Or(
            z3.And(z3.ULT(i, n), i_prime == i + z3.BitVecVal(1, 32)),
            z3.And(z3.UGE(i, n), i_prime == i)
        ),
        n_prime == n
    )
    
    # Safety property: i <= n
    post = z3.ULE(i, n)
    
    sts = TransitionSystem(
        variables=[i, n],
        prime_variables=[i_prime, n_prime],
        init=init,
        trans=trans,
        post=post
    )
    
    return sts


def run_demo_with_prover(sts: TransitionSystem, example_name: str, **kwargs) -> Dict[str, Any]:
    """Run demo using the LLM4InvProver"""
    logger.info(f"Running {example_name} with LLM4InvProver")
    
    prover = LLM4InvProver(sts, **kwargs)
    
    start_time = time.time()
    result = prover.solve()
    solve_time = time.time() - start_time
    
    stats = prover.get_statistics()
    stats['example_name'] = example_name
    stats['solve_time'] = solve_time
    
    if result.is_safe:
        logger.info(f"✓ {example_name}: Found invariant: {result.invariant}")
    else:
        logger.warning(f"✗ {example_name}: No invariant found")
    
    return stats


def main():
    """Main demo function"""
    logger.info("Starting LLM4Inv Demo")
    
    # Configuration
    config = {
        'timeout': 300,  # 5 minutes
        'max_iterations': 5,
        'max_candidates_per_iter': 3,
        'bit_width': 32,
        'llm_provider': 'local',  # Use local LLM
        'llm_model': 'qwen/qwen3-coder-30b',  # Local model name
        'temperature': 0.1,
        'max_output_length': 4096,
        'measure_cost': False,
        'local_provider': 'lm-studio'  # Local provider (lm-studio, vllm, sglang)
    }
    
    # Create examples
    examples = [
        ("Counter Example", create_counter_example()),
        ("Array Bounds Example", create_array_bounds_example())
    ]
    
    results = []
    
    for name, sts in examples:
        logger.info(f"\n{'='*50}")
        logger.info(f"Testing: {name}")
        logger.info(f"{'='*50}")
        
        # Test with LLM4InvProver (uses CEGIS internally)
        try:
            prover_stats = run_demo_with_prover(sts, name, **config)
            results.append(prover_stats)
        except Exception as e:
            logger.error(f"Error in {name}: {e}")
    
    # Print summary
    logger.info(f"\n{'='*50}")
    logger.info("DEMO SUMMARY")
    logger.info(f"{'='*50}")
    
    for stats in results:
        name = stats.get('example_name', 'Unknown')
        success = stats.get('success', False) or stats.get('is_safe', False)
        solve_time = stats.get('solve_time', 0)
        candidates = stats.get('tried_candidates', 0) or stats.get('total_candidates_generated', 0)
        
        status = "✓ SUCCESS" if success else "✗ FAILED"
        logger.info(f"{name}: {status} ({solve_time:.2f}s, {candidates} candidates)")


if __name__ == "__main__":
    import sys
    main()
