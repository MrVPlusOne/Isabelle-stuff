theory IMP
  imports Main 
    "~~/src/HOL/IMP/BExp"
begin
  
datatype
  com = SKIP 
      | Assign vname aexp       ("_ ::= _" [1000, 62] 62)
      | Seq    com  com         ("_;;/ _"  [60, 61] 60)
      | If     bexp com com     ("(IF _/ THEN _/ ELSE _)"  [0, 0, 63] 63)
      | While  bexp com         ("(WHILE _/ DO _)"  [0, 64] 64)
      | Repeat com bexp         ("(REPEAT _/ UNTIL _)" [0, 64] 64)
      | Or com com              ("(_/ OR _)" [61,62] 61)
        
value "SKIP OR WHILE b DO c ;; c2"

subsection "Big-Step Semantics of Commands"

text {*
The big-step semantics is a straight-forward inductive definition
with concrete syntax. Note that the first parameter is a tuple,
so the syntax becomes @{text "(c,s) \<Rightarrow> s'"}.
*}

text_raw{*\snip{BigStepdef}{0}{1}{% *}
inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip: "(SKIP,s) \<Rightarrow> s" |
Assign: "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Seq: "\<lbrakk> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
IfTrue: "\<lbrakk> bval b s;  (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:
"\<lbrakk> bval b s\<^sub>1;  (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> 
\<Longrightarrow> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3" |
RepeatTrue:
"\<lbrakk> bval b s\<rbrakk> \<Longrightarrow> (REPEAT c UNTIL b, s) \<Rightarrow> s" |
RepeatFalse:
"\<lbrakk> \<not>bval b s; (c, s) \<Rightarrow> s'; (REPEAT c UNTIL b, s') \<Rightarrow> t\<rbrakk> \<Longrightarrow> (REPEAT c UNTIL b, s) \<Rightarrow> t" |
OrL:
"(a,s) \<Rightarrow> t \<Longrightarrow> (a OR b, s) \<Rightarrow> t" |
OrR:
"(b,s) \<Rightarrow> t \<Longrightarrow> (a OR b, s) \<Rightarrow> t"
text_raw{*}%endsnip*}
  


text{* We want to execute the big-step rules: *}

code_pred big_step .

text{* For inductive definitions we need command
       \texttt{values} instead of \texttt{value}. *}

values "{t. (SKIP, \<lambda>_. 0) \<Rightarrow> t}"

text{* We need to translate the result state into a list
to display it. *}

values "{map t [''x''] |t. (SKIP, <''x'' := 42>) \<Rightarrow> t}"

values "{map t [''x''] |t. (''x'' ::= N 2, <''x'' := 42>) \<Rightarrow> t}"

values "{map t [''x'',''y''] |t.
  (WHILE Less (V ''x'') (V ''y'') DO (''x'' ::= Plus (V ''x'') (N 5)),
   <''x'' := 0, ''y'' := 13>) \<Rightarrow> t}"
  
values "{map t [''x'',''y''] |t.
  (REPEAT ''x'' ::= Plus (V ''x'') (N 5) UNTIL Not (Less (V ''x'') (V ''y'')),
   <''x'' := 0, ''y'' := 13>) \<Rightarrow> t}"
  
values "{map t [''x''] |t. (''x'' ::= N 2 OR ''x'' ::= N 3, <''x'' := 42>) \<Rightarrow> t}"
  


text{* Proof automation: *}

text {* The introduction rules are good for automatically
construction small program executions. The recursive cases
may require backtracking, so we declare the set as unsafe
intro rules. *}
declare big_step.intros [intro]
  thm big_step.intros

text{* The standard induction rule 
@{thm [display] big_step.induct [no_vars]} *}

thm big_step.induct

text{*
This induction schema is almost perfect for our purposes, but
our trick for reusing the tuple syntax means that the induction
schema has two parameters instead of the @{text c}, @{text s},
and @{text s'} that we are likely to encounter. Splitting
the tuple parameter fixes this:
*}
lemmas big_step_induct = big_step.induct[split_format(complete)]
thm big_step_induct
text {*
@{thm [display] big_step_induct [no_vars]}
*}


subsection "Rule inversion"

text{* What can we deduce from @{prop "(SKIP,s) \<Rightarrow> t"} ?
That @{prop "s = t"}. This is how we can automatically prove it: *}

inductive_cases SkipE[elim!]: "(SKIP,s) \<Rightarrow> t"
thm SkipE

text{* This is an \emph{elimination rule}. The [elim] attribute tells auto,
blast and friends (but not simp!) to use it automatically; [elim!] means that
it is applied eagerly.

Similarly for the other commands: *}

inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
thm AssignE
inductive_cases SeqE[elim!]: "(c1;;c2,s1) \<Rightarrow> s3"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
thm IfE

inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"
thm WhileE
  
inductive_cases RepeatE[elim]: "(REPEAT c UNTIL b, s) \<Rightarrow> t"
thm RepeatE
  
inductive_cases OrE[elim]: "(a OR b, s) \<Rightarrow> t"
thm OrE
  
  
text{* Only [elim]: [elim!] would not terminate. *}

text{* An automatic example: *}

lemma "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t \<Longrightarrow> t = s"
by blast

text{* Rule inversion by hand via the ``cases'' method: *}

lemma assumes "(IF b THEN SKIP ELSE SKIP, s) \<Rightarrow> t"
shows "t = s"
proof-
  from assms show ?thesis
  proof cases  --"inverting assms"
    case IfTrue thm IfTrue
    thus ?thesis by blast
  next
    case IfFalse thus ?thesis by blast
  qed
qed

(* Using rule inversion to prove simplification rules: *)
lemma assign_simp:
  "(x ::= a,s) \<Rightarrow> s' \<longleftrightarrow> (s' = s(x := aval a s))"
  by auto

text {* An example combining rule inversion and derivations *}
lemma Seq_assoc:
  "(c1;; c2;; c3, s) \<Rightarrow> s' \<longleftrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> s'"
proof
  assume "(c1;; c2;; c3, s) \<Rightarrow> s'"
  then obtain s1 s2 where
    c1: "(c1, s) \<Rightarrow> s1" and
    c2: "(c2, s1) \<Rightarrow> s2" and
    c3: "(c3, s2) \<Rightarrow> s'" by auto
  from c2 c3
  have "(c2;; c3, s1) \<Rightarrow> s'" by (rule Seq)
  with c1
  show "(c1;; (c2;; c3), s) \<Rightarrow> s'" by (rule Seq)
next
  -- "The other direction is analogous"
  assume "(c1;; (c2;; c3), s) \<Rightarrow> s'"
  thus "(c1;; c2;; c3, s) \<Rightarrow> s'" by auto
qed


subsection "Command Equivalence"

text {*
  We call two statements @{text c} and @{text c'} equivalent wrt.\ the
  big-step semantics when \emph{@{text c} started in @{text s} terminates
  in @{text s'} iff @{text c'} started in the same @{text s} also terminates
  in the same @{text s'}}. Formally:
*}
text_raw{*\snip{BigStepEquiv}{0}{1}{% *}
abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' \<equiv> (\<forall>s t. (c,s) \<Rightarrow> t  =  (c',s) \<Rightarrow> t)"
text_raw{*}%endsnip*}

text {*
Warning: @{text"\<sim>"} is the symbol written \verb!\ < s i m >! (without spaces).

  As an example, we show that loop unfolding is an equivalence
  transformation on programs:
*}
lemma unfold_while:
  "(WHILE b DO c) \<sim> (IF b THEN c;; WHILE b DO c ELSE SKIP)" (is "?w \<sim> ?iw")
proof (intro allI, rule)
  fix s t assume "(?w, s) \<Rightarrow> t" then show "(?iw, s) \<Rightarrow> t"
  proof cases
    case WhileFalse
    then show ?thesis by blast
  next
    case (WhileTrue s\<^sub>2)
    then show ?thesis by blast
  qed
next
  fix s t assume iw: "(?iw, s) \<Rightarrow> t" then show "(?w,s) \<Rightarrow> t"
  proof(cases "bval b s")
    case True
    then have "(c;; WHILE b DO c, s) \<Rightarrow> t" using iw by auto
    then obtain s' where "(c,s) \<Rightarrow> s'" and "(?w, s') \<Rightarrow> t" by blast
    then show "(?w, s) \<Rightarrow> t" using True by auto
  next
    case False
    then have "s=t" using iw by auto
    moreover have "(?w,s) \<Rightarrow> s" using False by auto
    ultimately show ?thesis by simp
  qed
qed
  
lemma Or_commute: "a OR b \<sim> b OR a"
  by blast
  

text {* Luckily, such lengthy proofs are seldom necessary.  Isabelle can
prove many such facts automatically.  *}

lemma while_unfold:
  "(WHILE b DO c) \<sim> (IF b THEN c;; WHILE b DO c ELSE SKIP)"
  by blast
    
lemma repeat_unfild:
  "(REPEAT c UNTIL b) \<sim> (IF b THEN SKIP ELSE c ;; (REPEAT c UNTIL b))"
  by blast

lemma triv_if:
  "(IF b THEN c ELSE c) \<sim> c"
by blast

lemma commute_if:
  "(IF b1 THEN (IF b2 THEN c11 ELSE c12) ELSE c2) 
   \<sim> 
   (IF b2 THEN (IF b1 THEN c11 ELSE c2) ELSE (IF b1 THEN c12 ELSE c2))"
by blast

lemma sim_while_cong_aux:
  "(WHILE b DO c,s) \<Rightarrow> t  \<Longrightarrow> c \<sim> c' \<Longrightarrow>  (WHILE b DO c',s) \<Rightarrow> t"
proof -
  assume wc:"(WHILE b DO c,s) \<Rightarrow> t" and "c \<sim> c'"
  then show "(WHILE b DO c',s) \<Rightarrow> t" (is "?w1 \<Rightarrow> t")
  proof (induction "WHILE b DO c" s t arbitrary: b c rule: big_step_induct)
    case (WhileFalse b s c)
    assume "\<not> bval b s"
    then show "(WHILE b DO c', s) \<Rightarrow> s" by (rule big_step.WhileFalse)
  next
    case (WhileTrue b s\<^sub>1 c s\<^sub>2 s\<^sub>3)
    then have "(c', s\<^sub>1) \<Rightarrow> s\<^sub>2" using `c \<sim> c'` by auto
    then show "(WHILE b DO c', s\<^sub>1) \<Rightarrow> s\<^sub>3" using WhileTrue by auto
  qed
qed        
        

lemma sim_while_cong: "c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b DO c'"
by (metis sim_while_cong_aux)

text {* Command equivalence is an equivalence relation, i.e.\ it is
reflexive, symmetric, and transitive. Because we used an abbreviation
above, Isabelle derives this automatically. *}

lemma sim_refl:  "c \<sim> c" by simp
lemma sim_sym:   "(c \<sim> c') = (c' \<sim> c)" by auto
lemma sim_trans: "c \<sim> c' \<Longrightarrow> c' \<sim> c'' \<Longrightarrow> c \<sim> c''" by auto

subsection "Execution is deterministic when no OR"
  
abbreviation "deterministic c \<equiv> \<forall> s t u. (c,s) \<Rightarrow> t \<and> (c,s) \<Rightarrow> u \<longrightarrow> t = u"
  
fun noOr::"com \<Rightarrow> bool" where
  "noOr (_ OR _) = False" |
  "noOr (_ ::= _) = True" |
  "noOr (a ;; b) = (noOr a \<and> noOr b)" |
  "noOr (IF _ THEN a ELSE b) = (noOr a \<and> noOr b)" |
  "noOr (WHILE _ DO c) = noOr c"|
  "noOr (REPEAT c UNTIL _) = noOr c" |
  "noOr SKIP = True"
    

text {* This proof is automatic. *}
  
(*lemma while_det: 
  assumes "deterministic c" 
  shows" deterministic (WHILE b DO c)"
    apply(induction "WHILE b DO c" rule: big_step_induct)
*)
theorem big_step_determ: "noOr c \<Longrightarrow> deterministic c"
proof(induction c rule: noOr.induct, auto)
  fix a s s1 s2 assume "deterministic a" "(a,s) \<Rightarrow> s1" "(a,s) \<Rightarrow> s2"
    then have "s1 = s2" by auto
    fix b t u assume "deterministic b" "(b, s1) \<Rightarrow> t" "(b, s2) \<Rightarrow> u"
    then show "t = u" using `s1 = s2` by auto
  next
    fix c s t u b
    assume "deterministic c" "(WHILE b DO c, s) \<Rightarrow> t" "(WHILE b DO c, s) \<Rightarrow> u"
    show "(WHILE b DO c, s) \<Rightarrow> t \<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> u \<Longrightarrow> t = u"
      apply(induction "WHILE b DO c" s t rule: big_step_induct
        
    
  by(induction c s t arbitrary: u rule: big_step_induct, blast+)
  
text {*
  This is the proof as you might present it in a lecture. The remaining
  cases are simple enough to be proved automatically:
*}
text_raw{*\snip{BigStepDetLong}{0}{2}{% *}
theorem
  "(c,s) \<Rightarrow> t  \<Longrightarrow>  (c,s) \<Rightarrow> t'  \<Longrightarrow>  t' = t"
proof (induction arbitrary: t' rule: big_step.induct)
  -- "the only interesting case, @{text WhileTrue}:"
  fix b c s s\<^sub>1 t t'
  -- "The assumptions of the rule:"
  assume "bval b s" and "(c,s) \<Rightarrow> s\<^sub>1" and "(WHILE b DO c,s\<^sub>1) \<Rightarrow> t"
  -- {* Ind.Hyp; note the @{text"\<And>"} because of arbitrary: *}
  assume IHc: "\<And>t'. (c,s) \<Rightarrow> t' \<Longrightarrow> t' = s\<^sub>1"
  assume IHw: "\<And>t'. (WHILE b DO c,s\<^sub>1) \<Rightarrow> t' \<Longrightarrow> t' = t"
  -- "Premise of implication:"
  assume "(WHILE b DO c,s) \<Rightarrow> t'"
  with `bval b s` obtain s\<^sub>1' where
      c: "(c,s) \<Rightarrow> s\<^sub>1'" and
      w: "(WHILE b DO c,s\<^sub>1') \<Rightarrow> t'"
    by auto
  from c IHc have "s\<^sub>1' = s\<^sub>1" by blast
  with w IHw show "t' = t" by blast
qed blast+ -- "prove the rest automatically"
text_raw{*}%endsnip*}
  
fun assigned :: "com \<Rightarrow> vname set" where
  "assigned (v ::= _) = {v}" |
  "assigned SKIP = {}" |
  "assigned (a;;b) = assigned a \<union> assigned b" |
  "assigned (IF b THEN c1 ELSE c2) = assigned c1 \<union> assigned c2" |
  "assigned (WHILE b DO c) = assigned c" |
  "assigned (REPEAT c UNTIL b) = assigned c"
  
lemma "\<lbrakk>(c, s) \<Rightarrow> t ; x \<notin> assigned c\<rbrakk> \<Longrightarrow> s x = t x"
  by(induction c s t rule: big_step_induct, auto)
    

inductive astep :: "aexp \<times> state \<Rightarrow> aexp \<Rightarrow> bool" (infix "\<leadsto>" 50) where
  "(V x, s) \<leadsto> N (s x)" |
  "(Plus (N a) (N b), _) \<leadsto> N (a + b)" |
  "(a, s) \<leadsto> a1 \<Longrightarrow> (Plus a b,s) \<leadsto> Plus a1 b" |
  "(b, s) \<leadsto> b1 \<Longrightarrow> (Plus (N a) b, s) \<leadsto> Plus (N a) b1"
  
lemmas astep_induct = astep.induct[split_format(complete)]
  
lemma "(a, s) \<leadsto> a' \<Longrightarrow> aval a s = aval a' s"
  by(induction a s a' rule: astep_induct, auto)
    
fun doWhile :: "bexp \<Rightarrow> com \<Rightarrow> com" where
  "doWhile b c = c ;; WHILE b DO c"
  
fun dewhile :: "com \<Rightarrow> com" where
  "dewhile SKIP = SKIP" |
  "dewhile (a::=b) = (a::=b)"|
  "dewhile (a;;b) = (dewhile a) ;; (dewhile b)"|
  "dewhile (IF b THEN c ELSE d) = (IF b THEN dewhile c ELSE dewhile d)"|
  "dewhile (WHILE b DO c) = IF b THEN doWhile b c ELSE SKIP" |
  "dewhile (REPEAT c UNTIL b) = IF b THEN SKIP ELSE doWhile (Not b) c"
  
lemma Repeat_suger: "(REPEAT c UNTIL b) \<sim> (WHILE (Not b) DO c)"
proof (intro allI, rule)
  fix s t assume "(REPEAT c UNTIL b, s) \<Rightarrow> t " then show " (WHILE bexp.Not b DO c, s) \<Rightarrow> t"
    proof(induction "REPEAT c UNTIL b" s t rule: big_step_induct)
      fix s assume "bval b s"
      then have "bval (Not b) s = False" by auto
      then show "(WHILE bexp.Not b DO c, s) \<Rightarrow> s" by auto
    next
      fix s s' t assume "\<not> bval b s"
      then have 1: "bval (Not b) s" by auto
      assume " (c, s) \<Rightarrow> s'" and "(WHILE bexp.Not b DO c, s') \<Rightarrow> t"
      then show "(WHILE bexp.Not b DO c, s) \<Rightarrow> t" using 1 by auto
    qed
next
  fix s t show "(WHILE bexp.Not b DO c, s) \<Rightarrow> t \<Longrightarrow> (REPEAT c UNTIL b, s) \<Rightarrow> t"
    by(induction "WHILE bexp.Not b DO c" s t rule: big_step_induct, auto)
qed

  
lemma "dewhile c \<sim> c"
  apply(induction c rule: dewhile.induct)
  by(auto simp add: Repeat_suger while_unfold)
    

  
  
  

end
