(* isabelle tutorial prog-prove Excercise 2.11 *)
theory Poly
  imports Main
begin

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var n = n" |
  "eval (Const n) _ = n" |
  "eval (Add e1 e2) n = eval e1 n + eval e2 n" |
  "eval (Mult e1 e2) n = eval e1 n * eval e2 n"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] _ = 0" |
  "evalp (p # ps) n = p + n * evalp ps n"

fun poly_add :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "poly_add [] ys = ys" |
  "poly_add xs [] = xs" |
  "poly_add (x#xs) (y#ys) = (x + y) # poly_add xs ys"

fun poly_mult :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "poly_mult [] _ = []" |
  "poly_mult _ [] = []" |
  "poly_mult (x#xs) ys = poly_add (map (op * x) ys) (0 # poly_mult xs ys)"

fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0, 1]" |
  "coeffs (Const n) = [n]" |
  "coeffs (Add e1 e2) = poly_add (coeffs e1) (coeffs e2)" |
  "coeffs (Mult e1 e2) = poly_mult (coeffs e1) (coeffs e2)"

lemma poly_add_spec [simp]: "evalp (poly_add xs ys) x = evalp xs x + evalp ys x"
  apply (induction rule: poly_add.induct)
    apply (auto simp add:algebra_simps)
  done

lemma mapmult_evalp [simp]: "evalp (map (op * a) xs) x = a * evalp xs x"
  apply (induction xs)
   apply (auto simp add:algebra_simps)
  done

lemma poly_mult_spec [simp]: "evalp (poly_mult xs ys) x = evalp xs x * evalp ys x"
  apply (induction rule: poly_mult.induct)
    apply (auto simp add:algebra_simps)
  done

theorem coeffs_spec : "evalp (coeffs e) x = eval e x"
  apply (induction e)
     apply (auto)
  done
