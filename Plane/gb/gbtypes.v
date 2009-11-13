Require Import ZArith.

Inductive term: Set := 
| Zero:term
| Const: Z -> positive -> term
| Var: positive -> term
| Opp: term -> term
| Add: term -> term -> term
| Sub: term -> term -> term
| Mul: term -> term -> term
| Pow: term -> positive -> term.

Inductive lineq: Set :=
  lnil: lineq
| lceq: term -> lineq -> lineq.

