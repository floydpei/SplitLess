# SplitLess

A distributed expense sharing system with formal TLA+ specifications and Python implementation, targetting a trusted group of friends.

## Repository Structure

- **`src/`** - Python implementation
  - **`main/`** - Core application code
  - **`data/`** - Replica storage

- **`TLA/SplitLess/`** - TLA+ specifications
  - **`SplitLess_replica_group_expenses`** - Current specification (replicas + groups + expenses)
  - Earlier versions (expenses-only, groups+expenses) are archived but not maintained

- **`TLC_test_results/`** - TLC model checker run screenshots for the largest verified models
- **`test_logs/`** - Probabilistic testing results of the Python implementation
- **`old_test_logs/`**, **`old_tlc_test_results/`** - Archived test results from previous versions

## TLA+ Specification

The current TLA+ specification is located in:
```
TLA/SplitLess/SplitLess_replica_group_expenses.tla
```

This version includes the complete specification with replicas, groups, and expenses. Earlier iterative versions exist in the same directory but are not maintained.

The toolbox settings for the largest model we verified are located in:
```
TLA/SplitLess/SplitLess_replica_group_expenses.toolbox/
```
The toolbox contains the constants defiend in the model and applies the correctness properties during model checking.

## Running the Python Application

To run the CLI, navigate to the `src/main` directory and execute:
```bash
python3 main.py
```

The CLI will guide you through:
1. Login/signup (basic, non-secure authentication)
2. Interactive SplitLess commands

After login/signup, use the `help` command within the CLI to see available commands.

## Probabilistic Testing

Test parameters can be configured by modifying the constants at the top of `test_runner.py`.
To run the probabilistic tester, navigate to the `src/main` directory and execute:
```bash
python3 test_runner.py
```

Enable temporal property checking (slower):
```bash
python3 test_runner.py --do_temp_check
```
