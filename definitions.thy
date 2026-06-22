(*<*)
theory definitions
  imports Main "HOL.Rat" "HOL-Library.LaTeXsugar" base
begin
(*>*)




text \<open>Eine Position ist kohärent, wenn sie vollständig und konsistent ist und ebenfalls alle Argumente
der Debatte erfüllt.\<close>
definition coherent :: "position \<Rightarrow> ds \<Rightarrow> bool" (infix "\<Turnstile>" 65)
  where "coherent P ds = (complete P \<and> consistent P  \<and> ( \<forall>a \<in> ds. models_arg P a))"

text \<open>mods gibt bezüglich einer partiellen Position P, die Menge aller vollständigen, kohärenten
Positionen an, in welchen P enthalten ist.
\#Info mods P sind alle Modelle der Debatte, in welchen die Literale von P enthalten sind.\<close>
definition mods :: "position \<Rightarrow> ds \<Rightarrow> position set" where
"mods P ds = {V . P \<subseteq> V \<and> V \<Turnstile> ds}"

abbreviation all_mods where "all_mods \<equiv> mods {}"

subsection \<open>Orginale Definitionen der DoJ\<close>

definition coherent_partial :: "position \<Rightarrow> ds \<Rightarrow> bool"
  where "coherent_partial P ds = (mods P ds \<noteq> {})"

definition satisfiable :: "ds \<Rightarrow> bool"
  where "satisfiable ds = (\<exists>P . P \<Turnstile> ds)"

definition \<sigma> :: "position \<Rightarrow> ds \<Rightarrow> nat"
  where "\<sigma> P ds =  card (mods P ds)"

definition doj_cond :: "position \<Rightarrow> position \<Rightarrow> ds \<Rightarrow> rat"
  where "doj_cond P Q ds =  (rat_of_nat (\<sigma> (P \<union> Q) ds) ) / ( rat_of_nat (\<sigma> Q ds))"

definition doj :: "position \<Rightarrow> ds \<Rightarrow> rat"
  where "doj P \<equiv> doj_cond P {}"

(*>*)
end
(*>*)
