theory PropLogic
  imports Main
begin
  
    
datatype formula =
  V string |
  NOT formula |
  And formula formula (infix "AND" 203) |
  Or formula formula (infix "OR" 202) |
  Imp formula formula (infix "\<rightarrow>" 201)
  
fun Iff ::"formula \<Rightarrow> formula \<Rightarrow> formula" (infix "\<leftrightarrow>" 200) where
  "Iff a b = (a \<rightarrow> b) AND (b \<rightarrow> a)"
  
  
type_synonym state = "string \<Rightarrow> bool"
  
fun evalFol :: "formula \<Rightarrow> state \<Rightarrow> bool" where
  "evalFol (V n) s = s n" |
  "evalFol (NOT f) s = (\<not> evalFol f s)" |
  "evalFol (a AND b) s = (evalFol a s \<and> evalFol b s)" |
  "evalFol (a OR b) s = (evalFol a s \<or> evalFol b s)" |
  "evalFol (a \<rightarrow> b) s = (evalFol a s \<longrightarrow> evalFol b s)"
  
fun nnfNot :: "formula \<Rightarrow> formula" where
  "nnfNot (NOT a) = a" |
  "nnfNot (a OR b) = (nnfNot a AND nnfNot b)" |
  "nnfNot (a AND b) = (nnfNot a OR nnfNot b)" |
  "nnfNot other = NOT other"
  
fun toNNF :: "formula \<Rightarrow> formula" where
  "toNNF (V s) = V s" |
  "toNNF (NOT f) = nnfNot (toNNF f)" |
  "toNNF (a AND b) = toNNF a AND toNNF b" |
  "toNNF (a OR b) = toNNF a OR toNNF b" |
  "toNNF (a \<rightarrow> b) = nnfNot (toNNF a) OR toNNF b"
  
abbreviation equiv :: "formula \<Rightarrow> formula \<Rightarrow> bool" (infix "\<sim>" 199) where
 "a \<sim> b \<equiv> (\<forall>s. evalFol a s = evalFol b s)"
  
value "toNNF (NOT (V ''p'' \<rightarrow> V ''p'' AND V ''q''))"
  
lemma nnfNot_equiv: "evalFol (nnfNot f) s = (\<not> evalFol f s)"
  by(induction f rule: nnfNot.induct, auto)
  
lemma nnf_equiv: "toNNF f \<sim> f"
  by(induction f rule: toNNF.induct, auto simp add: nnfNot_equiv)
  
text{* function to test if a formula is in NNF *}
  
fun inNNF :: "formula \<Rightarrow> bool" where
  "inNNF (V v) = True" |
  "inNNF (NOT (V a)) = True" |
  "inNNF (NOT _) = False" |
  "inNNF (a AND b) = (inNNF a \<and> inNNF b)" |
  "inNNF (a OR b) = (inNNF a \<and> inNNF b)" |
  "inNNF (_ \<rightarrow> _) = False"
      
lemma nnfNot_preserve_inNNF: "inNNF f \<Longrightarrow> inNNF (nnfNot f)"
  by(induction f rule: inNNF.induct, auto)
  
lemma nnf_inNNF: "inNNF (toNNF f)" using nnfNot_preserve_inNNF
  by(induction f, auto)
    
text{* test if a formula is in DNF *}
  
fun noAnd :: "formula \<Rightarrow> bool" where
  "noAnd (V _) = True" |
  "noAnd (_ AND _) = False" |
  "noAnd (a OR b) = (noAnd a \<and> noAnd b)" |
  "noAnd (NOT v) = noAnd v" |
  "noAnd (a \<rightarrow> b) = (noAnd a \<and> noAnd b)"
  
fun distrAndOverOr_and :: "formula \<Rightarrow> formula \<Rightarrow> formula" where
  "distrAndOverOr_and (f1 OR f2) f3 = (distrAndOverOr_and f1 f3 OR distrAndOverOr_and f2 f3)" |
  "distrAndOverOr_and f3 (f1 OR f2) = (distrAndOverOr_and f3 f1 OR distrAndOverOr_and f3 f2)" |
  "distrAndOverOr_and a b = a AND b"
  
lemma distrAndOverOr_and_equiv : "distrAndOverOr_and a b \<sim> (a AND b)"
  by(induction a b rule: distrAndOverOr_and.induct, auto)
  
fun distrAndOverOr :: "formula \<Rightarrow> formula" where
  "distrAndOverOr (a AND b) = distrAndOverOr_and (distrAndOverOr a) (distrAndOverOr b)" |
  "distrAndOverOr (a OR b) = (distrAndOverOr a) OR distrAndOverOr b" |
  "distrAndOverOr (a \<rightarrow> b) = (distrAndOverOr a) \<rightarrow> distrAndOverOr b" |
  "distrAndOverOr other = other"
  
lemma distrAndOverOr_equiv: "distrAndOverOr f \<sim> f"
  using distrAndOverOr_and_equiv
  by(induction f rule: distrAndOverOr.induct, auto)
  
fun toDNF :: "formula \<Rightarrow> formula" where
  "toDNF f = distrAndOverOr (toNNF f)"
    
value "toDNF ((V ''q1'' OR NOT (NOT (V ''q2''))) AND (NOT (V ''r1'') \<rightarrow> V ''r2''))"
  
lemma toDNF_equiv: "toDNF f \<sim> f"
proof-
  have "toDNF f \<sim> toNNF f" using distrAndOverOr_equiv by auto
  then show ?thesis using nnf_equiv by auto
qed
  
value "toDNF ((V ''1'' OR V ''2'' ) AND (V ''3'' OR V ''4'' ))"
  
fun distrOrOverAnd_or :: "formula \<Rightarrow> formula \<Rightarrow> formula" where
  "distrOrOverAnd_or (f1 AND f2) f3 = (distrOrOverAnd_or f1 f3 AND distrOrOverAnd_or f2 f3)" |
  "distrOrOverAnd_or f3 (f1 AND f2) = (distrOrOverAnd_or f3 f1 AND distrOrOverAnd_or f3 f2)" |
  "distrOrOverAnd_or a b = a OR b"
  
    
lemma distrOrOverAnd_or_equiv : "distrOrOverAnd_or a b \<sim> (a OR b)"
  by(induction a b rule: distrOrOverAnd_or.induct, auto)
  
fun distrOrOverAnd :: "formula \<Rightarrow> formula" where
  "distrOrOverAnd (a OR b) = distrOrOverAnd_or (distrOrOverAnd a) (distrOrOverAnd b)" |
  "distrOrOverAnd (a AND b) = (distrOrOverAnd a) AND distrOrOverAnd b" |
  "distrOrOverAnd (a \<rightarrow> b) = (distrOrOverAnd a) \<rightarrow> distrOrOverAnd b" |
  "distrOrOverAnd other = other"
  
lemma distrOrOverAnd_equiv: "distrOrOverAnd f \<sim> f"
  using distrOrOverAnd_or_equiv 
    by (induction f rule: distrOrOverAnd.induct, auto)
  
fun toCNF :: "formula \<Rightarrow> formula" where
  "toCNF f = distrOrOverAnd (toNNF f)"
  
lemma[simp]: "toCNF f \<sim> f"
  using distrOrOverAnd_equiv nnf_equiv by auto
    
  
text {* convert (p \<leftrightarrow> (q \<rightarrow> r )) to CNF *}
value "toCNF (V ''p'' \<leftrightarrow> (V ''q'' \<rightarrow> V ''r'' ))"
  
abbreviation "satisfiable f \<equiv> \<exists>c. evalFol f c"
  
lemma "satisfiable (V ''p'' AND NOT (V ''q''))"
proof
  show "evalFol (V ''p'' AND NOT (V ''q'')) ((\<lambda>x. True)(''q'' := False))" by auto
qed
  
  
  
  
    
end
  