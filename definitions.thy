(*<*)
theory definitions
  imports Main "HOL.Rat" "HOL-Library.LaTeXsugar"
begin
(*>*)


section Definitionen

text \<open>Ein Satz ist dabei eine atomare Aussage innerhalb einer Debatte.
Im folgenden werden Sätz per Konvention immer mit x, y, s dargestellt.\<close>
typedecl sentence

text \<open>Ein Satz kann in der Debatte entweder negiert oder nicht negiert auftreten.
Im folgenden werden Literale per Konvention immer mit l, k dargestellt.
Eine Premisse mit p, eine Menge an Premissen mit ps und eine Konklusion mit c\<close>
datatype literal = Pos (sen:sentence) | Neg (sen:sentence)


text \<open>Ein Argument ist ein Tupel von Prämissen und einer Konklusion.\<close>
type_synonym argument = "(literal set) \<times> literal"

abbreviation fact :: "literal \<Rightarrow> argument" where "fact l \<equiv> ({},l)"

text \<open>Eine Debatte ist eine Menge von Argumenten\<close>
type_synonym ds = "argument set"

text \<open>Eine Position ist eine Menge von Literalen\<close>
type_synonym position = "literal set"

text \<open>Das Komplement eines Literal ist sein Gegenteil. (Pos -> Neg, Neg -> Pos)\<close>
fun compl_lit :: "literal \<Rightarrow> literal"
  where "compl_lit (Pos s) = Neg s"
      | "compl_lit (Neg s) = Pos s"

text \<open>Die Domain einer Position / eines Arguments / einer Debatte, ist die Menge der Sätze,
über welche Aussagen getroffen werden.\<close>
fun domain_pos :: "position \<Rightarrow> sentence set" where
"domain_pos P = image sen P"

fun domain_arg :: "argument \<Rightarrow> sentence set"  where
"domain_arg (ps, c) = image sen (ps \<union> {c})"

fun domain_ds :: "ds \<Rightarrow> sentence set" where
"domain_ds ds = \<Union>(image domain_arg ds)" (* \<Union> for flattening *)

text \<open>Eine Position ist vollständig, wenn sie über alle Sätze des Universums Aussagen trifft.
\#Info Diese Anforderung macht die coherent Relation linkstotal.\<close>
definition complete :: "position \<Rightarrow> bool" where
  "complete P = (\<forall>s . \<exists> l \<in> P. sen l = s)"

text \<open>Eine Position ist konsistent, wenn sie über den gleichen Satz keine unterschiedlichen Aussagen trifft.
\#Info Diese Anforderung macht die coherent Relation rechtseindeutig.\<close>
definition consistent:: "position \<Rightarrow> bool" where
  "consistent P = (\<forall>s  . \<not>(Neg s \<in> P \<and> Pos s \<in> P))"

typedef ccPosition  = "{P :: position. consistent P \<and> complete P}"
   using consistent_def complete_def literal.sel(1) 
   by (metis literal.disc(1) literal.disc_eq_case(2) literal.simps(6) mem_Collect_eq)

lemma x: "\<forall>p \<in> ccPosition . \<exists>pos :: position . p = pos" by auto


text \<open>Ein Argument hat die Form einer Implikation. Wenn die Prämissen in der Position enthalten sind,
erfüllt die Position das Argument, wenn die Konklusion ebenfalls entfalten ist. Wenn die Position
das Komplement einer Prämisse enthält, erfüllt die Position ebenfalls das Argument.
\#Info Wenn die Position dem Argument erfüllt, dann modelliert die Interpretation P das Argument\<close>
fun models_arg :: "ccPosition \<Rightarrow> argument \<Rightarrow> bool"
  where "models_arg P (ps,c) = (ps \<subseteq> Rep_ccPosition P \<longrightarrow> c \<in> Rep_ccPosition P)"

text \<open>Eine Position ist kohärent, wenn sie vollständig und konsistent ist und ebenfalls alle Argumente
der Debatte erfüllt.\<close>
definition coherent :: "ccPosition \<Rightarrow> ds \<Rightarrow> bool" (infix "\<Turnstile>" 65)
  where "coherent P ds = (\<forall>a \<in> ds. models_arg P a)"

locale DoJ = 
  fixes ds :: "ds"
  assumes finsen: "finite (UNIV :: sentence set)"
      and sat: "\<exists>P . P \<Turnstile> ds"

context DoJ
begin

text \<open>mods gibt bezüglich einer partiellen Position P, die Menge aller vollständigen, kohärenten
Positionen an, in welchen P enthalten ist.
\#Info mods P sind alle Modelle der Debatte, in welchen die Literale von P enthalten sind.\<close>
definition mods :: "ccPosition  \<Rightarrow> ccPosition set" where
"mods P  = {V . Rep_ccPosition P \<subseteq> Rep_ccPosition V \<and>  V\<Turnstile> ds}"

abbreviation all_mods where "all_mods \<equiv> mods {}"

subsection \<open>Orginale Definitionen der DoJ\<close>

definition coherent_partial :: "position \<Rightarrow> bool"
  where "coherent_partial P  = (mods P  \<noteq> {})"

definition \<sigma> :: "position \<Rightarrow> nat"
  where "\<sigma> P  =  card (mods P)"

definition doj_cond :: "position \<Rightarrow> position \<Rightarrow> rat"
  where "doj_cond P Q =  (rat_of_nat (\<sigma> (P \<union> Q) ) ) / ( rat_of_nat (\<sigma> Q))"

definition doj :: "position  \<Rightarrow> rat"
  where "doj P \<equiv> doj_cond P {}"

(*>*)
end
end
(*>*)
