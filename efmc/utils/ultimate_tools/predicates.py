"""
Predicate utilities migrated from Ultimate's Library-ModelCheckerUtils.

TODO: migrated by LLM, need to check
"""

from abc import ABC, abstractmethod
from typing import Optional, List, Dict, Any
import z3


class IAbstractPredicate(ABC):
    @abstractmethod
    def get_formula(self) -> z3.ExprRef: pass
    @abstractmethod
    def get_closed_formula(self) -> z3.ExprRef: pass


class IPredicate(IAbstractPredicate):
    def get_closed_formula(self) -> z3.ExprRef: return self.get_formula()


class BasicPredicate(IPredicate):
    def __init__(self, formula: z3.ExprRef): self._formula = formula
    def get_formula(self) -> z3.ExprRef: return self._formula
    def __str__(self) -> str: return str(self._formula)
    def __repr__(self) -> str: return f"BasicPredicate({self._formula})"
    def __eq__(self, other) -> bool: return isinstance(other, BasicPredicate) and z3.eq(self._formula, other._formula)
    def __hash__(self) -> int: return hash(str(self._formula))


class AbsIntPredicate(IPredicate):
    def __init__(self, formula: z3.ExprRef, domain: str = "unknown"):
        self._formula = formula
        self._domain = domain
    
    def get_formula(self) -> z3.ExprRef: return self._formula
    def get_domain(self) -> str: return self._domain
    def __str__(self) -> str: return f"AbsIntPredicate({self._formula}, domain={self._domain})"


class ISLPredicate(IPredicate):
    def __init__(self, formula: z3.ExprRef, smtlib_string: str = ""):
        self._formula = formula
        self._smtlib_string = smtlib_string
    
    def get_formula(self) -> z3.ExprRef: return self._formula
    def get_smtlib_string(self) -> str: return self._smtlib_string
    def set_smtlib_string(self, smtlib_string: str): self._smtlib_string = smtlib_string
    def __str__(self) -> str: return f"ISLPredicate({self._smtlib_string or self._formula})"


class UnknownState(IPredicate):
    def __init__(self): self._formula = z3.BoolVal(False)
    def get_formula(self) -> z3.ExprRef: return self._formula
    def __str__(self) -> str: return "UnknownState"
    def __repr__(self) -> str: return "UnknownState()"


class PredicateTree:
    def __init__(self, predicate: IPredicate, children: Optional[List['PredicateTree']] = None):
        self.predicate = predicate
        self.children = children or []
    
    def add_child(self, child: 'PredicateTree'): self.children.append(child)
    
    def get_all_predicates(self) -> List[IPredicate]:
        result = [self.predicate]
        for child in self.children:
            result.extend(child.get_all_predicates())
        return result
    
    def get_depth(self) -> int:
        if not self.children: return 0
        return 1 + max(child.get_depth() for child in self.children)
    
    def __str__(self) -> str: return self._to_string(0)
    
    def _to_string(self, indent: int) -> str:
        result = "  " * indent + str(self.predicate)
        for child in self.children:
            result += "\n" + child._to_string(indent + 1)
        return result


class IPredicateUnifier(ABC):
    @abstractmethod
    def unify_predicates(self, predicates: List[IPredicate]) -> List[IPredicate]: pass
    @abstractmethod
    def get_unification_statistics(self) -> Dict[str, Any]: pass


class BasicPredicateUnifier(IPredicateUnifier):
    def __init__(self):
        self._unification_count = 0
        self._total_predicates = 0
    
    def unify_predicates(self, predicates: List[IPredicate]) -> List[IPredicate]:
        if not predicates: return []
        
        self._total_predicates += len(predicates)
        unified = []
        
        for pred in predicates:
            is_redundant = False
            for existing_pred in unified:
                if self._is_implied_by(pred, existing_pred):
                    is_redundant = True
                    self._unification_count += 1
                    break
                elif self._is_implied_by(existing_pred, pred):
                    unified.remove(existing_pred)
                    unified.append(pred)
                    self._unification_count += 1
                    is_redundant = True
                    break
            
            if not is_redundant:
                unified.append(pred)
        
        return unified
    
    def _is_implied_by(self, pred1: IPredicate, pred2: IPredicate) -> bool:
        formula1, formula2 = pred1.get_formula(), pred2.get_formula()
        solver = z3.Solver()
        solver.add(z3.And(formula2, z3.Not(formula1)))
        return solver.check() == z3.unsat
    
    def get_unification_statistics(self) -> Dict[str, Any]:
        return {
            "unification_count": self._unification_count,
            "total_predicates": self._total_predicates,
            "unification_ratio": (self._unification_count / max(1, self._total_predicates))
        }


class IDomainSpecificOperationProvider(ABC):
    @abstractmethod
    def get_domain_name(self) -> str: pass
    @abstractmethod
    def can_handle_predicate(self, predicate: IPredicate) -> bool: pass
    @abstractmethod
    def perform_operation(self, predicate: IPredicate, operation: str, **kwargs) -> Optional[IPredicate]: pass


class PredicateFactory:
    @staticmethod
    def create_basic_predicate(formula: z3.ExprRef) -> BasicPredicate: return BasicPredicate(formula)
    @staticmethod
    def create_absint_predicate(formula: z3.ExprRef, domain: str = "interval") -> AbsIntPredicate:
        return AbsIntPredicate(formula, domain)
    @staticmethod
    def create_isl_predicate(formula: z3.ExprRef, smtlib_string: str = "") -> ISLPredicate:
        return ISLPredicate(formula, smtlib_string)
    @staticmethod
    def create_unknown_state() -> UnknownState: return UnknownState()
    @staticmethod
    def create_true_predicate() -> BasicPredicate: return BasicPredicate(z3.BoolVal(True))
    @staticmethod
    def create_false_predicate() -> BasicPredicate: return BasicPredicate(z3.BoolVal(False)) 