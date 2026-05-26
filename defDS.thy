theory defDS
  imports Main  "HOL.Rat"
begin

(* Im folgenden werden Sätz per Konvention immer mit x, y, s dargestellt *)
typedecl sentence

(* Im folgenden werden Literale per Konvention immer mit l, k dargestellt.
Eine Premisse mit p, eine Menge an Premissen mit ps. Eine Konklusion mit c*)
datatype literal = Pos (sen:sentence) | Neg (sen:sentence)

axiomatization where
  finsen: "finite (UNIV :: sentence set)"

(* Argumente haben die Kennzeichnung A, B *)
type_synonym argument = "(literal set) \<times> literal"

(* eine Dialektische Struktur hat per Konvention immer die Kennzeichnung ds" *)
type_synonym ds = "argument set"

(* Positionen werden immer groß geschrieben. Eine vollständige Position hat die Kennzeichnung V.
Eine Partielle Position die Kennzeichnung P, Q *)
type_synonym position = "literal set"

(* Alle Sätze über die die Position P eine Aussage trifft *)
fun domain_pos :: "position \<Rightarrow> sentence set" where
"domain_pos P = {s. \<exists>l \<in> P . sen l = s }"

(* Alle Sätze über die ein Argument eine Aussage trifft *)
fun domain_arg :: "argument \<Rightarrow> sentence set"  where
"domain_arg (ps, c) = {s. \<exists>l \<in> ps \<union> {c} . sen l = s}" 

(* Alle Sätze über die die Dialektische Struktur eine Aussage trifft *)
fun domain_ds :: "ds \<Rightarrow> sentence set" where
"domain_ds ds = {s. \<exists>a \<in> ds . s \<in> domain_arg a}"

(* linkstotal *)
definition complete :: "position \<Rightarrow> ds \<Rightarrow> bool" where
  "complete P ds = (\<forall>s . \<exists> l \<in> P. sen l = s)"

(* rechtseindeutig *)
definition consistent:: "position \<Rightarrow> ds \<Rightarrow> bool" where
  "consistent P ds = (\<forall>s  . \<not>(Neg s \<in> P \<and> Pos s \<in> P))"

definition complete_consistent :: "position \<Rightarrow> ds \<Rightarrow> bool"
  where "complete_consistent P ds = (complete P ds \<and> consistent P ds)"

fun models_arg :: "position \<Rightarrow> argument \<Rightarrow> bool"
  where "models_arg P (ps,c) = (ps \<subseteq> P \<longrightarrow> c \<in> P)"

definition coherent :: "position \<Rightarrow> ds \<Rightarrow> bool" (infix "\<Turnstile>" 65)
  where "coherent P ds = (complete_consistent P ds \<and> ( \<forall>a \<in> ds. models_arg P a))"

definition mods :: "position \<Rightarrow> ds \<Rightarrow> position set" where
"mods P ds = {V . P \<subseteq> V \<and> V \<Turnstile> ds}"

definition coherent_extensions where "coherent_extensions \<equiv> mods"

definition coherent_partial :: "position \<Rightarrow> ds \<Rightarrow> bool"
  where "coherent_partial P ds = (coherent_extensions P ds \<noteq> {})"

definition satisfiable :: "ds \<Rightarrow> bool"
  where "satisfiable ds = (\<exists>P . P \<Turnstile> ds)"


definition \<sigma> :: "position \<Rightarrow> ds \<Rightarrow> nat"
  where "\<sigma> P ds =  card (mods P ds)"


definition doj_cond :: "position \<Rightarrow> position \<Rightarrow> ds \<Rightarrow> rat"
  where "doj_cond Q P ds =  (of_nat (\<sigma> (P \<union> Q) ds) :: rat) / ( of_nat (\<sigma> Q ds) :: rat)"

definition doj :: "position \<Rightarrow> ds \<Rightarrow> rat"
  where "doj \<equiv> doj_cond {}"

definition compl_pos :: "position \<Rightarrow> position"
  where "compl_pos P = image (\<lambda>x :: literal .if x = Pos (sen x) then Neg (sen x) else Pos (sen x)) P"

lemma finite_positions:
  shows "finite (UNIV :: position)"
proof -
  have "((UNIV :: literal set) = range Pos \<union> range Neg)"
    by (metis literal.exhaust UNIV_eq_I Un_iff rangeI)
  thus ?thesis
    using finsen by (metis finite_Un finite_imageI) 
qed


lemma fin_mods:
"finite (mods P ds)"
proof -
  show ?thesis
    using finite_positions
    using Finite_Set.finite_set infinite_super subset_UNIV
   by blast
qed

end








