"""
Simplified LLM4Inv Prover

This module implements the main LLM4InvProver class that integrates the
"LLM proposes structure, SMT fills holes" paradigm into the efmc framework.
"""

import logging
import time
from typing import Optional, Dict, Any, List

import z3

from efmc.sts import TransitionSystem
from efmc.utils.verification_utils import VerificationResult
from .cegis_loop import CEGISLoop
from .template_dsl import TemplateParser
from .template_completion import TemplateCompletion
from .llm_interface import LLMInterface

logger = logging.getLogger(__name__)


class LLM4InvProver:
    """
    Simplified LLM4Inv prover implementing the "LLM proposes structure, SMT fills holes" paradigm.
    
    This prover uses a hybrid approach where:
    1. LLM generates invariant template structures
    2. SMT solver completes templates by finding concrete values for holes
    3. CEGIS loop iteratively refines templates based on counterexamples
    """
    
    def __init__(self, sts: TransitionSystem, **kwargs):
        self.sts = sts
        
        # Core configuration
        self.timeout = kwargs.get('timeout', 600)
        self.max_iterations = kwargs.get('max_iterations', 10)
        self.bit_width = kwargs.get('bit_width', 32)
        self.llm_model = kwargs.get('llm_model', 'deepseek-v3')
        self.smt_solver = kwargs.get('smt_solver', 'z3api')
        self.validate_results = kwargs.get('validate_results', True)
        
        # Initialize components
        self._initialize_components()
        
        # Statistics
        self.solve_time = 0
        self.result = None
        
    def _initialize_components(self):
        """Initialize all components with current configuration"""
        config = {
            'timeout': self.timeout,
            'max_iterations': self.max_iterations,
            'bit_width': self.bit_width,
            'llm_model': self.llm_model,
            'smt_solver': self.smt_solver,
            'validate_results': self.validate_results
        }
        
        # Initialize CEGIS loop (which initializes other components)
        self.cegis_loop = CEGISLoop(self.sts, **config)
        
        # Direct access to components for convenience
        self.llm_interface = self.cegis_loop.llm_interface
        self.template_completion = self.cegis_loop.template_completion
        
        # Initialize parser for utility functions
        self.parser = TemplateParser(self.bit_width)
        var_dict = {str(var): var for var in self.sts.variables}
        self.parser.set_variables(var_dict)
    
    def solve(self, timeout: Optional[int] = None) -> VerificationResult:
        """
        Main solving method using CEGIS loop.
        
        Args:
            timeout: Optional timeout override
            
        Returns:
            VerificationResult with the synthesized invariant
        """
        if timeout is not None:
            self.timeout = timeout
            self.cegis_loop.timeout = timeout
        
        start_time = time.time()
        
        try:
            logger.info("Starting LLM4Inv synthesis")
            
            # Generate program description for LLM
            program_description = self._generate_program_description()
            
            # Run CEGIS loop
            invariant = self.cegis_loop.synthesize_invariant(program_description)
            
            self.solve_time = time.time() - start_time
            
            if invariant is not None:
                logger.info(f"LLM4Inv synthesis successful in {self.solve_time:.2f}s")
                self.result = VerificationResult(True, invariant)
                return self.result
            else:
                logger.info(f"LLM4Inv synthesis failed after {self.solve_time:.2f}s")
                self.result = VerificationResult(False, reason="Synthesis failed")
                return self.result
                
        except Exception as e:
            logger.error(f"LLM4Inv synthesis error: {e}")
            self.solve_time = time.time() - start_time
            self.result = VerificationResult(False, reason=f"Error: {e}")
            return self.result
    
    def _generate_program_description(self) -> str:
        """Generate program description for LLM"""
        description = []
        
        # Add variable information
        variables = list(self.sts.variables.keys())
        description.append(f"Variables: {', '.join(variables)}")
        
        # Add bit width information
        description.append(f"Bit width: {self.bit_width}")
        
        # Add basic transition system information
        description.append("Program behavior:")
        description.append("- Initial condition defines starting states")
        description.append("- Transition relation defines state changes")
        description.append("- Safety property must hold in all reachable states")
        
        return "\n".join(description)
    
    def generate_templates(self, program_code: str = "") -> List[str]:
        """
        Generate templates using LLM interface.
        
        Args:
            program_code: Optional program description
            
        Returns:
            List of template strings
        """
        templates = self.llm_interface.generate_templates(program_code)
        return [self._template_to_string(t) for t in templates]
    
    def complete_template(self, template_str: str) -> Optional[z3.ExprRef]:
        """
        Complete a single template string.
        
        Args:
            template_str: Template string to complete
            
        Returns:
            Completed invariant or None if completion fails
        """
        template = self.parser.parse_template(template_str)
        if template is None:
            logger.warning(f"Failed to parse template: {template_str}")
            return None
        
        return self.template_completion.complete_template(template)
    
    def _template_to_string(self, template) -> str:
        """Convert template object to string representation"""
        # Simplified string conversion
        atom_strs = []
        for atom in template.atoms:
            atom_strs.append(f"{atom.atom_type.name}")
        
        connector = " && " if template.conjunction else " || "
        return connector.join(atom_strs)
    
    def get_statistics(self) -> Dict[str, Any]:
        """Get comprehensive prover statistics"""
        stats = {
            'solve_time': self.solve_time,
            'timeout': self.timeout,
            'max_iterations': self.max_iterations,
            'bit_width': self.bit_width,
            'llm_model': self.llm_model,
            'smt_solver': self.smt_solver,
            'success': self.result.is_safe if self.result else False
        }
        
        # Add CEGIS statistics
        if hasattr(self.cegis_loop, 'get_statistics'):
            stats['cegis_stats'] = self.cegis_loop.get_statistics()
        
        # Add component statistics
        if hasattr(self.llm_interface, 'get_statistics'):
            stats['llm_stats'] = self.llm_interface.get_statistics()
        
        if hasattr(self.template_completion, 'get_statistics'):
            stats['completion_stats'] = self.template_completion.get_statistics()
        
        return stats
    
    def set_timeout(self, timeout: int):
        """Set timeout for all components"""
        self.timeout = timeout
        self.cegis_loop.timeout = timeout
        self.template_completion.timeout = timeout
    
    def set_llm_model(self, model_name: str):
        """Set LLM model and reinitialize components"""
        self.llm_model = model_name
        self._initialize_components()
    
    def set_smt_solver(self, solver_name: str):
        """Set SMT solver and reinitialize components"""
        self.smt_solver = solver_name
        self._initialize_components()
    
    def reset(self):
        """Reset prover state"""
        self.solve_time = 0
        self.result = None
        self.cegis_loop.reset()
    
    def __str__(self) -> str:
        return f"LLM4InvProver(model={self.llm_model}, solver={self.smt_solver}, timeout={self.timeout})"
    
    def __repr__(self) -> str:
        return self.__str__() 