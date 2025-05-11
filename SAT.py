import time
import threading
import os
import tracemalloc
import pycosat
import copy
from collections import defaultdict
from typing import List, Dict, Optional, Tuple
from sympy import to_cnf, Or, And
from sympy.parsing.sympy_parser import parse_expr
from sympy import Implies, Equivalent

def measure_formula_memory_and_time(run_fn, *args):
    tracemalloc.start()
    start_time = time.time()
    result = run_fn(*args)
    end_time = time.time()
    current, peak = tracemalloc.get_traced_memory()
    tracemalloc.stop()
    elapsed_time = end_time - start_time
    return result, elapsed_time, peak / 1024
def convert_to_expr_with_implication_support(expr: str) -> str:
    expr = expr.replace("<->", " Equivalent ")
    expr = expr.replace(">>", " Implies ")
    return expr

def run_with_timeout(func, args=(), timeout=8):
    result = [None]

    def wrapper():
        try:
            result[0] = func(*args)
        except:
            result[0] = None

    thread = threading.Thread(target=wrapper)
    thread.start()
    thread.join(timeout)
    if thread.is_alive():
        return None, True
    return result[0], False

def _eliminate(var: int, clauses: List[List[int]]) -> Optional[List[List[int]]]:

    pos = [c for c in clauses if  var in c]
    neg = [c for c in clauses if -var in c]
    rest = [c for c in clauses if  var not in c and -var not in c]

    resolvents: List[List[int]] = []
    for p in pos:
        for n in neg:
            resolvent = [x for x in set(p + n) if x not in (var, -var)]

            if not resolvent:
                return None

            if any(-lit in resolvent for lit in resolvent):
                continue
            resolvents.append(resolvent)

    uniq, seen = [], set()
    for c in rest + resolvents:
        key = tuple(sorted(c))
        if key not in seen:
            seen.add(key)
            uniq.append(c)
    return uniq

def parse_dimacs_cnf(file_path: str):
    clauses = []
    with open(file_path, 'r') as file:
        for line in file:
            line = line.strip()
            if not line or line.startswith(('c', 'p', '%')):
                continue
            try:
                tokens = list(map(int, line.split()))
                if tokens and tokens[-1] == 0:
                    tokens = tokens[:-1]
                if tokens:
                    clauses.append(tokens)
            except ValueError:
                continue
    return clauses

def _neg(lit: int) -> int:
    return -lit

def _new_watches(clause: List[int], assignment: Dict[int, bool]) -> Tuple[int, int]:
    w1 = w2 = -1
    for lit in clause:
        val = assignment.get(abs(lit))
        if val is None or val == (lit > 0):
            if w1 == -1:
                w1 = lit
            elif w2 == -1:
                w2 = lit
                break
    return w1, w2

def expr_to_cnf_clauses(expr: str) -> Tuple[int, List[List[int]], Dict[str, int]]:
    sympy_expr = to_cnf(parse_expr(expr, evaluate=False), simplify=True)
    var_mapping = {}
    index = 1

    def map_var(v):
        nonlocal index
        v = str(v)
        if v not in var_mapping:
            var_mapping[v] = index
            index += 1
        return var_mapping[v]

    def clause_to_dimacs(clause):
        if isinstance(clause, Or):
            return [map_var(arg) if arg.is_Atom else -map_var(arg.args[0]) for arg in clause.args]
        elif clause.is_Atom:
            return [map_var(clause)]
        else:
            return [-map_var(clause.args[0])]

    if isinstance(sympy_expr, And):
        clauses = [clause_to_dimacs(arg) for arg in sympy_expr.args]
    else:
        clauses = [clause_to_dimacs(sympy_expr)]
    return index - 1, clauses, var_mapping


def dpll_simple(clauses: List[List[int]], assignment: Dict[int, bool] = {}) -> Optional[Dict[int, bool]]:
    if not clauses:
        return assignment
    if [] in clauses:
        return None
    for clause in clauses:
        if len(clause) == 1:
            lit = clause[0]
            val = lit > 0
            var = abs(lit)
            assignment[var] = val
            new_clauses = []
            for c in clauses:
                if lit in c:
                    continue
                new_c = [l for l in c if l != -lit]
                if not new_c:
                    return None
                new_clauses.append(new_c)
            return dpll_simple(new_clauses, assignment)
    for clause in clauses:
        for lit in clause:
            var = abs(lit)
            if var not in assignment:
                for val in [True, False]:
                    new_assignment = assignment.copy()
                    new_assignment[var] = val
                    new_clauses = [c[:] for c in clauses] + [[var if val else -var]]
                    result = dpll_simple(new_clauses, new_assignment)
                    if result is not None:
                        return result
                return None
    return assignment


def cdcl_final(clauses: List[List[int]]) -> Optional[Dict[int, bool]]:
    assignment = {}
    decision_stack = []
    learned_clauses = []

    def is_satisfied(clause):
        return any((lit > 0 and assignment.get(abs(lit), False)) or
                   (lit < 0 and not assignment.get(abs(lit), True))
                   for lit in clause)

    def has_conflict():
        for clause in clauses + learned_clauses:
            if all((lit > 0 and assignment.get(abs(lit), False) is False) or
                   (lit < 0 and assignment.get(abs(lit), True) is True)
                   for lit in clause):
                return clause
        return None

    def unit_propagate():
        changed = True
        while changed:
            changed = False
            for clause in clauses + learned_clauses:
                unassigned = [lit for lit in clause if abs(lit) not in assignment]
                satisfied = any((lit > 0 and assignment.get(abs(lit), False)) or
                                (lit < 0 and not assignment.get(abs(lit), True))
                                for lit in clause)
                if satisfied:
                    continue
                if len(unassigned) == 1:
                    lit = unassigned[0]
                    assignment[abs(lit)] = lit > 0
                    decision_stack.append((abs(lit), lit > 0, "unit"))
                    changed = True
                elif not unassigned:
                    return clause  # conflict
        return None

    def choose_literal():
        for clause in clauses + learned_clauses:
            for lit in clause:
                if abs(lit) not in assignment:
                    return abs(lit)
        return None

    while True:
        conflict = unit_propagate()
        if conflict:
            learned_clauses.append(conflict)
            while decision_stack:
                var, val, reason = decision_stack.pop()
                del assignment[var]
                if reason == "decision":
                    assignment[var] = not val
                    decision_stack.append((var, not val, "flip"))
                    break
            else:
                return None

        else:
            var = choose_literal()
            if var is None:
                if all(is_satisfied(c) for c in clauses + learned_clauses):
                    return assignment
                return None
            assignment[var] = True
            decision_stack.append((var, True, "decision"))

def cdcl_simple(clauses: List[List[int]]) -> Optional[Dict[int, bool]]:
    return cdcl_final([c[:] for c in clauses])
def resolution_simple(clauses: List[List[int]]) -> bool:
    new = set()
    clauses_set = [frozenset(c) for c in clauses]

    while True:
        pairs = [(clauses_set[i], clauses_set[j]) for i in range(len(clauses_set)) for j in range(i + 1, len(clauses_set))]
        for ci, cj in pairs:
            for lit in ci:
                if -lit in cj:
                    resolvent = (ci - {lit}) | (cj - {-lit})
                    if not resolvent:
                        return False
                    new.add(frozenset(resolvent))
        if new.issubset(set(clauses_set)):
            return True
        clauses_set.extend(c for c in new if c not in clauses_set)
        new.clear()


def dp_simple(clauses: List[List[int]]) -> bool:
    clauses = [c for c in clauses if not any(-l in c for l in c)]

    while True:
        if [] in clauses:
            return False
        if not clauses:
            return True

        # Unit propagation
        unit_literals = {c[0] for c in clauses if len(c) == 1}
        while unit_literals:
            lit = unit_literals.pop()
            new_clauses = []
            for clause in clauses:
                if lit in clause:
                    continue
                if -lit in clause:
                    new_clause = [l for l in clause if l != -lit]
                    if not new_clause:
                        return False
                    new_clauses.append(new_clause)
                else:
                    new_clauses.append(clause)
            clauses = new_clauses
            unit_literals |= {c[0] for c in clauses if len(c) == 1}

        flat = [lit for c in clauses for lit in c]
        for lit in set(flat):
            if -lit not in flat:  # pure literal
                clauses = [c for c in clauses if lit not in c]
                break
        else:
            pivot = abs(flat[0])
            clauses = _eliminate(pivot, clauses)
            if clauses is None:
                return False


def dpll_verbose(clauses: List[List[int]], assignment: Dict[int, bool] = {}, depth=0) -> Optional[Dict[int, bool]]:
    indent = "    " * depth
    print(f"{indent}[DPLL] Clauses: {clauses}")
    print(f"{indent}[DPLL] Current assignment: {assignment}")

    if not clauses:
        print(f"{indent}[DPLL] All clauses satisfied. Returning SAT.")
        return assignment

    if [] in clauses:
        print(f"{indent}[DPLL] Empty clause found. Backtracking.")
        return None

    # Unit clause propagation
    for clause in clauses:
        if len(clause) == 1:
            lit = clause[0]
            val = lit > 0
            var = abs(lit)
            print(f"{indent}[DPLL] Unit clause: {clause}. Assigning {var} = {val}")
            assignment[var] = val
            new_clauses = []
            for c in clauses:
                if lit in c:
                    continue
                new_c = [l for l in c if l != -lit]
                if not new_c:
                    print(f"{indent}[DPLL] Conflict after propagation. Backtracking.")
                    return None
                new_clauses.append(new_c)
            return dpll_verbose(new_clauses, assignment, depth)

    # Decision making
    for clause in clauses:
        for lit in clause:
            var = abs(lit)
            if var not in assignment:
                for val in [True, False]:
                    print(f"{indent}[DPLL] Trying {var} = {val}")
                    new_assignment = assignment.copy()
                    new_assignment[var] = val
                    new_clauses = [c[:] for c in clauses] + [[var if val else -var]]
                    result = dpll_verbose(new_clauses, new_assignment, depth + 1)
                    if result is not None:
                        return result
                print(f"{indent}[DPLL] Backtracking on {var}")
                return None
    return assignment


def resolution_verbose(clauses: List[List[int]]) -> bool:
    print("\n[Resolution] Starting resolution method")
    print("[Resolution] Initial clauses:")
    for c in clauses:
        print(f"  {c}")

    new = set()
    clauses_set = [frozenset(c) for c in clauses]

    while True:
        pairs = [(clauses_set[i], clauses_set[j]) for i in range(len(clauses_set)) for j in range(i + 1, len(clauses_set))]
        for ci, cj in pairs:
            for lit in ci:
                if -lit in cj:
                    resolvent = (ci - {lit}) | (cj - {-lit})
                    print(f"[Resolution] Resolving {set(ci)} and {set(cj)} on {lit} → {set(resolvent)}")
                    if not resolvent:
                        print("[Resolution] UNSATISFIABLE.")
                        return False
                    new.add(frozenset(resolvent))
        if new.issubset(set(clauses_set)):
            print("[Resolution] SATISFIABLE.")
            return True
        clauses_set.extend(c for c in new if c not in clauses_set)
        new.clear()

def dp_super_verbose(clauses: List[List[int]]) -> Optional[Dict[int, bool]]:

    import copy, time

    start = time.time()

    sat = dp_simple(copy.deepcopy(clauses))
    dur = time.time() - start

    if not sat:
        print(f"[DP]  {dur:.4f}s  →   UNSAT")
        return None

    print(f"[DP] {dur:.4f}s  →   SAT")

    if "dpll_simple" in globals():
        model = globals()["dpll_simple"](copy.deepcopy(clauses))
    else:
        model = {"SAT": True}

    return model


def how_to_use():
    print("\n=== HOW TO USE THIS SAT SOLVER ===\n")
    print("✔ This program solves SAT problems using 4 methods:")
    print("   - DPLL")
    print("   - Resolution")
    print("   - CDCL (Conflict-Driven Clause Learning)")
    print("   - DP (Davis–Putnam)\n")
    print("✔ You can choose:")
    print("   1. Benchmark file (.cnf in DIMACS format) or your own file with the same structure")
    print("   2. Your own logical formula( Like those we used last semester during the LCS course\n")
    print(" When writing your own formula:")
    print("   - Use variables like A, B, C... avoid E, I, O (because they are reserved in SymPy and you will get an error)")
    print("   - Use the following operators:")
    print("       ∧ → &     (AND)")
    print("       ∨ → |     (OR)")
    print("       ¬ → ~     (NOT)")
    print("       → → >>   (IMPLIES)")
    print("       ↔ → <->   (EQUIVALENT)")
    print("   - Example: (A | ~B) & (B | C)\n")
    print("✔ Output includes step-by-step tracing for each algorithm.")
    print("✔ The CNF form of your formula will be displayed for clarity.\n")
    print("Have fun solving logic like a boss!\n")

def test_with_pycosat(clauses):
    print("[DEBUG] Calling pycosat with:", clauses)
    try:
        result = pycosat.solve(clauses)
        print("[DEBUG] Raw result from pycosat:", result)
        return "UNSAT" if result == "UNSAT" else "SAT"
    except Exception as e:
        print("[ERROR] PycoSAT crashed:", e)
        return "ERROR"

def run_all(clauses: List[List[int]]):
    print("\n====================")
    print("Solving the formula")
    print("====================\n")

    def run_method(name, func):
        tracemalloc.start()
        start = time.time()
        result = func([c[:] for c in clauses])
        duration = time.time() - start
        _, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()
        memory_kb = peak / 1024
        print(f"{name}: {'SAT' if result else 'UNSAT'}")
        print(f"Time: {duration:.5f}s")
        print(f"Memory used: {memory_kb:.2f} KB\n")

    run_method("PycoSAT", lambda cls: test_with_pycosat(cls))
    run_method("DPLL", lambda cls: dpll_verbose(cls))
    run_method("Resolution", lambda cls: resolution_verbose(cls))
    run_method("CDCL", lambda cls: cdcl_final(cls))
    run_method("DP", lambda cls: dp_super_verbose(cls))


def run_benchmarks_summary(folder_path: str):
    print("\n=== Running Benchmarks Summary ===")
    files = [f for f in os.listdir(folder_path) if f.endswith(".cnf")]
    if not files:
        print("No .cnf files found.")
        return

    stats = {
        "DPLL": {"SAT": 0, "UNSAT": 0, "TIMEOUT": 0, "time": 0.0, "mem": 0.0},
        "Resolution": {"SAT": 0, "UNSAT": 0, "TIMEOUT": 0, "time": 0.0, "mem": 0.0},
        "CDCL": {"SAT": 0, "UNSAT": 0, "TIMEOUT": 0, "time": 0.0, "mem": 0.0},
        "DP": {"SAT": 0, "UNSAT": 0, "TIMEOUT": 0, "time": 0.0, "mem": 0.0},
    }

    for file in files:
        file_path = os.path.join(folder_path, file)
        print(f"\n {file}")
        try:
            _, clauses = parse_dimacs_cnf(file_path)


            # DPLL
            start = time.time()
            result = dpll_verbose([c[:] for c in clauses])
            res = "SAT" if result else "UNSAT"
            print(f"  DPLL: {res} ({time.time() - start:.5f}s)")
            stats["DPLL"][res] += 1

            # Resolution
            start = time.time()
            result = resolution_verbose([c[:] for c in clauses])
            res = "SAT" if result else "UNSAT"
            print(f"  Resolution: {res} ({time.time() - start:.5f}s)")
            stats["Resolution"][res] += 1

            # CDCL
            start = time.time()
            result = cdcl_final([c[:] for c in clauses])
            res = "SAT" if result else "UNSAT"
            print(f"  CDCL: {res} ({time.time() - start:.5f}s)")
            stats["CDCL"][res] += 1

            # DP
            start = time.time()
            result = dp_super_verbose([c[:] for c in clauses])
            res = "SAT" if result else "UNSAT"
            print(f"  DP: {res} ({time.time() - start:.5f}s)")
            stats["DP"][res] += 1

        except Exception as e:
            print(f" Error in file {file}: {e}")

    print("\n=== Summary of Results ===")
    for method, result in stats.items():
        print(f"{method}: SAT = {result['SAT']}, UNSAT = {result['UNSAT']}")



def run_multi_formula_file(file_path: str):
    import threading

    def run_with_timeout(func, args=(), timeout=8):
        result = [None]

        def wrapper():
            try:
                result[0] = func(*args)
            except:
                result[0] = None

        thread = threading.Thread(target=wrapper)
        thread.start()
        thread.join(timeout)
        if thread.is_alive():
            return None, True
        return result[0], False

    print(f"\n=== Running Multi-Formula CNF File: {file_path} ===")
    all_stats = {
        "Pycosat": {"SAT": 0, "UNSAT": 0},
        "DPLL": {"SAT": 0, "UNSAT": 0, "TIMEOUT": 0, "time": 0.0, "mem": 0.0},
        "Resolution": {"SAT": 0, "UNSAT": 0, "TIMEOUT": 0, "time": 0.0, "mem": 0.0},
        "CDCL": {"SAT": 0, "UNSAT": 0, "TIMEOUT": 0, "time": 0.0, "mem": 0.0},
        "DP": {"SAT": 0, "UNSAT": 0, "TIMEOUT": 0, "time": 0.0, "mem": 0.0},
    }

    formulas = []
    current = []

    with open(file_path, 'r') as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith(('c', '%')):
                continue
            elif line.startswith('p'):
                if current:
                    formulas.append(current)
                current = []
                continue
            try:
                clause = list(map(int, line.split()))
                clause = [x for x in clause if x != 0]
                if clause:
                    current.append(clause)
            except ValueError:
                continue
        if current:
            formulas.append(current)

    print(f"→ Total formulas detected: {len(formulas)}")

    for idx, clauses in enumerate(formulas):
        print(f"\nFormula #{idx + 1}")

        # DPLL
        tracemalloc.start()
        start = time.time()
        result = dpll_simple([c[:] for c in clauses])
        dur = time.time() - start
        current, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()

        res = "SAT" if result else "UNSAT"
        all_stats["DPLL"][res] += 1
        all_stats["DPLL"]["time"] += dur
        all_stats["DPLL"]["mem"] += peak / 1024


        tracemalloc.start()
        start = time.time()
        result, to = run_with_timeout(resolution_simple, ([c[:] for c in clauses],), timeout=8)
        dur = time.time() - start
        current, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()

        if to:
            all_stats["Resolution"]["TIMEOUT"] += 1
        else:
            verdict = "SAT" if result else "UNSAT"
            all_stats["Resolution"][verdict] += 1

        all_stats["Resolution"]["time"] += dur
        all_stats["Resolution"]["mem"] += peak / 1024  # memory in KB
        # CDCL
        tracemalloc.start()
        start = time.time()
        result = cdcl_simple([c[:] for c in clauses])
        dur = time.time() - start
        current, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()

        all_stats["CDCL"]["SAT" if result else "UNSAT"] += 1
        all_stats["CDCL"]["time"] += dur
        all_stats["CDCL"]["mem"] += peak / 1024

        tracemalloc.start()
        start = time.time()
        result, to = run_with_timeout(dp_simple, ([c[:] for c in clauses],), timeout=8)
        dur = time.time() - start
        current, peak = tracemalloc.get_traced_memory()
        tracemalloc.stop()

        if to:
            all_stats["DP"]["TIMEOUT"] += 1
        else:
            verdict = "SAT" if result else "UNSAT"
            all_stats["DP"][verdict] += 1

        all_stats["DP"]["time"] += dur
        all_stats["DP"]["mem"] += peak / 1024

    print("\n=== FINAL SUMMARY ===")
    print(f"{'Method':<12} | {'SAT':<4} | {'UNSAT':<6} | {'TIMEOUT':<8} | {'Time (s)':<10} | {'Memory (KB)':<12}")
    print("-" * 75)
    for method in ["DPLL", "Resolution", "CDCL", "DP"]:
        s = all_stats[method]
        print(f"{method:<12} | {s['SAT']:<4} | {s['UNSAT']:<6} | {s['TIMEOUT']:<8} | {s['time']:.5f}    | {s['mem']:.2f}")

def main():
    print("SAT Solver (Step-by-Step Tracing)")
    print("1. Use benchmark (.cnf file)")
    print("2. Enter your own logical formula")
    print("3. How to use")

    choice = input("Choose an option (1/2/3): ").strip()

    if choice == "1":
        path = input("Enter path to a .cnf file: ").strip()
        if os.path.isdir(path):
            run_benchmarks_summary(path)
            return
        elif os.path.isfile(path) and path.endswith(".cnf"):
            run_multi_formula_file(path)
            return
        else:
            print("Invalid path. Must be a .cnf file.")
            return

    elif choice == "2":
        expr = input("Enter formula (e.g., (A | ~B) & (B | C)): ").strip()
        from sympy import to_cnf
        from sympy.parsing.sympy_parser import parse_expr
        parsed_expr = parse_expr(expr, evaluate=False, local_dict={"Implies": Implies, "Equivalent": Equivalent})
        cnf_expr = to_cnf(parsed_expr, simplify=False)
        pretty_cnf = str(cnf_expr).replace("Or", "∨").replace("And", "∧").replace("~", "¬").replace(",", "")
        print("\nCNF format:")
        print(pretty_cnf, "\n")
        _, clauses, _ = expr_to_cnf_clauses(expr)
        run_all(clauses)

    elif choice == "3":
        how_to_use()


    else:
        print("Invalid choice.")


if __name__ == "__main__":
    main()
