theory HW3
  imports Complex
begin
  
text {* 1(a): The product of an odd and even integer is even. *}
  
lemma "even (e::int) \<Longrightarrow> odd s \<Longrightarrow> even (e * s)"
proof-
  fix e:: int and s
  assume "even e"
  then obtain k where "2*k = e"
    using evenE by auto
  then have "e * s = (2*k)*s" by simp
  moreover have "\<dots> = 2 * (k*s)" by simp
  moreover have "even \<dots>" by auto
  ultimately show "even (e*s)" by auto
qed
  
text {* 1(b): If r is a rational number and p is an irrational number, then r+p is irrational. *}
    
  
lemma rewrite1:
  fixes q1 q2 r1 r2 :: int 
  assumes n0: "q2 \<noteq>0" "r2\<noteq>0"
  shows "q1/q2-r1/r2 = (q1*r2-r1*q2)/(q2*r2)" (is ?goal)
proof -
  have "q1/q2 - r1/r2 = q1*r2 / (q2*r2) - (r1*q2)/(q2*r2)" using n0 by simp
  moreover have "\<dots> = (q1*r2-r1*q2)/(q2*r2)" by (simp add: diff_divide_distrib)
  ultimately show ?goal by linarith
qed
  
  
abbreviation rational :: "real \<Rightarrow> bool" where
  "rational n \<equiv> \<exists>(p::int) (q::int). n = p / q \<and> q\<noteq>0 "
  
lemma 
  assumes r:"rational r" 
    and p:" \<not>(rational p)"
  shows " \<not>(rational (r+p))"
proof
  from r obtain r1::int and r2::int where 1:"r = r1/r2" "r2\<noteq>0" using of_int_0 by blast
  assume "rational (r+p)"
  hence "rational (r1/r2+p)" using 1 by simp
  then obtain q1::int and q2::int where 2:"r1/r2+p = q1/q2" "q2\<noteq>0" using of_int_0 by blast
  hence "p = q1/q2-r1/r2" by simp
  hence "p = (q1*r2-r1*q2)/(q2*r2)" using `q2 \<noteq> 0` `r2 \<noteq> 0` rewrite1 by auto
  moreover have "(q2*r2)\<noteq>0" using `q2 \<noteq> 0` `r2 \<noteq> 0` by auto
  ultimately have "rational p" using of_int_0 by fastforce
  thus False using p by simp
qed
  
text {* 1(c): If r is a rational number and p is an irrational number, then rp is irrational*} 
text {* To prove this, we need r\<noteq>0 *}
  
lemma 
  assumes r: "rational r" and "r\<noteq>0"
    and p: "\<not>(rational p)"
  shows "\<not>(rational (r * p))"
proof
  from r obtain r1::int and r2::int where 1:"r = r1/r2" "r2\<noteq>0" using of_int_0 by blast
  hence "r1\<noteq>0" using `r\<noteq>0` by auto
  assume "rational (r*p)"
  hence "rational (r1*p/r2)" using 1 by simp
  then obtain q1::int and q2::int where 2:"r1*p/r2 = q1/q2" "q2\<noteq>0" using of_int_0 by blast
  hence "r1 * p / r2 * r2 = q1 / q2 * r2" by auto
  hence "r1 * p = q1 / q2 * r2" using 1 by auto
  hence "r1*p/r1 = q1/q2*r2/r1" using `q2 \<noteq> 0` `r2 \<noteq> 0` by auto
  hence "p = q1/q2*r2/r1" using `r1\<noteq>0` by auto
  hence "p = (q1*r2)/(q2*r1)" by auto
  moreover have "q2*r1 \<noteq> 0" using `q2\<noteq>0` `r1\<noteq>0` by auto
  ultimately have "rational p"
    using of_int_eq_0_iff by blast
  thus False using p by auto
qed
  
      
text {* 1(d): If 7x+9 is even, then x is odd *}
  
lemma 
assumes 1: "even (7*x+9)" shows "odd (x::int)"
proof
  assume "even x"
  hence "even (7*x)" by auto
  hence "odd (7*x+9)" by auto
  thus False using 1 by auto
qed
  
text {* 1(e): For all real numbers, max(a, max(b,c)) = max(max(a,b), c) *}
lemma
  fixes a::real and b::real and c::real
  shows "max a (max b c) = max (max a b) c"
  by(unfold max_def, auto)
    
text {* 4: A \<union> (A \<inter> B) = A *}
  
lemma "A \<union> (A \<inter> B) = A"
proof
  show " A \<union> A \<inter> B \<subseteq> A"
  proof
    fix x assume "x \<in> A \<union> A \<inter> B"
    thus "x \<in> A" by auto
  qed
next
  text {* Similarly... *}
  show "A \<subseteq> A \<union> A \<inter> B" by auto
qed
  
text {* 5: *}
  
lemma "\<exists>x. \<forall>y. P x y \<longleftrightarrow> \<not>(P y y) \<Longrightarrow> False" (is "?A \<Longrightarrow> False")
proof-
  assume "?A"
  then obtain x where 1: "\<forall>y. P x y \<longleftrightarrow> \<not>(P y y)" by blast
  hence "P x x \<longleftrightarrow> \<not>(P x x)" by blast
  thus False by auto
qed
  

    
    
  
    