(*<*)
theory base
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


text \<open>Eine Debatte ist endlich, also ist das Universum der Sätze endlich.\<close>
axiomatization where
  finsen: "finite (UNIV :: sentence set)"

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


text \<open>Ein Argument hat die Form einer Implikation. Wenn die Prämissen in der Position enthalten sind,
erfüllt die Position das Argument, wenn die Konklusion ebenfalls entfalten ist. Wenn die Position
das Komplement einer Prämisse enthält, erfüllt die Position ebenfalls das Argument.
\#Info Wenn die Position dem Argument erfüllt, dann modelliert die Interpretation P das Argument\<close>
fun models_arg :: "position \<Rightarrow> argument \<Rightarrow> bool"
  where "models_arg P (ps,c) = (ps \<subseteq> P \<longrightarrow> c \<in> P)"

end