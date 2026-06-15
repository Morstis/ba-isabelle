(*<*)
theory probability
  imports Main  "HOL.Rat" "HOL-Library.LaTeXsugar"  definitions theorems
begin
declare [[quick_and_dirty = true]]
(*>*)

section \<open>Begrundsgrade als Wahrscheinlichkeiten\<close>

text \<open>Wir definieren einen Grundraum bezüglich einer Debatte.
\#Philo Der Grundraum ist die Menge aller vollständigen kohärenten Positionen.
\#Info Der Grundraum ist die Menge aller Modelle der Debatte\<close>
definition \<Omega> :: "ds \<Rightarrow> position set" where
  "\<Omega> ds = mods {} ds"

text \<open>Der Grundraum sollte nicht leer sein. Das ist genau dann der Fall, wenn ds erfüllbar ist. \<close>
lemma "satisfiable ds \<longleftrightarrow> card(\<Omega> ds) > 0" 
  (*<*)
  using satisfiable_def \<Omega>_def mods_def bot.extremum bot_nat_0.not_eq_extremum card_Diff1_less fin_mods less_nat_zero_code mem_Collect_eq
  by (metis (mono_tags, lifting) Collect_empty_eq card_gt_0_iff)
(*>*)

axiomatization where
  not_empty: "card (\<Omega> ds) > 0"

text \<open>Wir definieren die normierte Funktion Pr bezüglich des Grundraums als die
1. Philo Kardinalität einer Menge partiell kohärenter Positionen,
2. Info Kardinalität einer Menge von partiellen Modellen.\<close>
definition Pr :: "position set \<Rightarrow> ds \<Rightarrow> rat"
  where "Pr Ps ds = rat_of_nat (card (Ps \<inter> \<Omega> ds)) / (rat_of_nat (card (\<Omega> ds)))"

text \<open>Die bedingte Wahrscheinlichkeit ist folgendermaßen definiert.\<close>
definition Pr_cond 
  where "Pr_cond P B ds = Pr (P \<inter> B) ds / Pr B ds"

(*<*)
lemma Pr_cond_simp [simp]:
  "Pr_cond P B ds = rat_of_nat (card (P \<inter> B \<inter> \<Omega> ds)) / rat_of_nat (card (B \<inter> \<Omega> ds))"
  unfolding Pr_cond_def Pr_def using not_empty by simp

lemma omega_inter [simp]: "mods P ds \<inter> \<Omega> ds = mods P ds"
  using \<Omega>_def mods_def by auto
(*>*)

text \<open>Trivialerweise ist Pr in [0, 1]\<close>
lemma between0_1:
  shows "0 \<le> Pr Ps ds \<and> Pr Ps ds \<le> 1"
(*<*)
proof -
  have "0 \<le> Pr Ps ds" by (simp add: Pr_def)
  also have "Pr Ps ds \<le> 1"
    proof -
        have "Ps \<inter> \<Omega> ds \<subseteq> \<Omega> ds" by simp
        hence "card (Ps \<inter> \<Omega> ds) \<le> card (\<Omega> ds)"
        by (simp add: \<Omega>_def card_mono fin_mods)
        thus ?thesis
        by (metis Pr_def less_divide_eq_1 linorder_not_le of_nat_le_iff
            of_nat_less_0_iff)
    qed

  ultimately show ?thesis by simp
qed
(*>*)

text \<open>Trivialerweise ist Pr vom Grundraum 1\<close>
lemma \<Omega>_one:
  shows "Pr (\<Omega> ds) ds = 1"
  using not_empty by (simp add: Pr_def)

(*<*)
lemma sigma_subadd:
  assumes subsets: "\<forall>n. (A n :: position set) \<subseteq> \<Omega> ds"
  assumes "finite I"
  shows "Pr (\<Union>n \<in> I . A n ) ds \<le> (\<Sum>n \<in> I . (Pr (A n) ds))"
proof -
  have  "(card (\<Union>n \<in> I . (A n) \<inter> \<Omega> ds)) \<le> (\<Sum>n \<in> I . card ((A n) \<inter> \<Omega> ds))"
    using card_UN_le assms(2) by blast
  thus ?thesis unfolding  Pr_def
  proof -
    show "rat_of_nat (card (\<Union> (A ` I) \<inter> \<Omega> ds)) / rat_of_nat (card (\<Omega> ds)) \<le> (\<Sum>a\<in>I. rat_of_nat (card (A a \<inter> \<Omega> ds)) / rat_of_nat (card (\<Omega> ds)))"
      by (metis (no_types) SUP_inf \<open>card (\<Union>n\<in>I. A n \<inter> \<Omega> ds) \<le> (\<Sum>n\<in>I. card (A n \<inter> \<Omega> ds))\<close> divide_right_mono of_nat_0_le_iff of_nat_le_iff of_nat_sum sum_divide_distrib)
  qed
qed
(*>*)

text \<open>Trivialerweise gilt die Simga-Additivität\<close>
lemma sigma_add:
  assumes subsets: "\<forall>n. (A n :: position set) \<subseteq> \<Omega> ds"
  assumes disjoint: "\<forall>i j. i \<noteq> j \<longrightarrow> (A i) \<inter> (A j) = {}"
  assumes fin: "finite I"
  shows "Pr (\<Union>n \<in> I . A n ) ds = (\<Sum>n \<in> I . (Pr (A n) ds))"
(*<*)
proof -
  have "\<forall>i \<in> I. finite (A i)" using fin_mods \<Omega>_def 
    by (metis infinite_super subsets)
  hence  "(card (\<Union>n \<in> I . (A n) \<inter> \<Omega> ds)) = (\<Sum>n \<in> I . card ((A n) \<inter> \<Omega> ds))"
    using card_UN_disjoint fin disjoint 
    by (smt (verit, ccfv_SIG) inf.idem inf_le2 le_inf_iff subset_antisym subsets sum.cong)


  thus ?thesis unfolding Pr_def
    by (simp add: sum_divide_distrib)
qed
(*>*)

text \<open>Dadurch ist Pr ein diskretes Wahrscheinlich-keitsmaß\<close>


subsection \<open>doj ist Pr\<close>
text \<open>Wählen wir als Ereignis die Menge aller Modelle, die Position P  erweitern (mods P ds), 
dann ist Pr (mods P ds) ds der doj von Gregor. Gleiches gilt für die bedingen dojs\<close>
theorem doj_pr:
  shows "doj P ds = Pr (mods P ds) ds"
proof -
  have "mods P ds \<inter> \<Omega> ds = mods P ds" using mods_def \<Omega>_def by auto
  thus ?thesis unfolding doj_def doj_cond_def Pr_def \<sigma>_def \<Omega>_def
    by simp
qed


theorem doj_cond_pr_cond:
  shows "doj_cond P B ds = Pr_cond (mods P ds) (mods B ds) ds"
(*<*)
proof -
  have mods_sub: "\<forall>p . mods p ds \<subseteq> \<Omega> ds" using \<Omega>_def mods_def by auto
  have cap_union: "\<forall>A B . (mods (A \<union> B) ds) = (mods A ds \<inter> mods B ds)" unfolding mods_def 
    by blast
  have "Pr (mods P ds \<inter> mods B ds) ds / Pr (mods B ds) ds 
    = rat_of_nat (card (mods P ds \<inter> mods B ds \<inter> \<Omega> ds)) / rat_of_nat (card (mods B ds \<inter> \<Omega> ds))"
    unfolding Pr_def
    using not_empty by auto
  also have "... = rat_of_nat (card (mods P ds \<inter> mods B ds)) / rat_of_nat (card (mods B ds))" 
    using mods_sub  by (simp add: inf_absorb1 inf_assoc)
  also have "... = rat_of_nat (card (mods (P \<union> B) ds)) / rat_of_nat (card (mods B ds))"
    using cap_union by auto
  finally show ?thesis unfolding doj_cond_def \<sigma>_def Pr_cond_def by simp
qed
(*>*)

subsection \<open>weitere Theoreme\<close>

text \<open>Es gilt der Satz der Totalen Wahrscheinlichkeit. (noch nicht bewiesen in Isabelle)\<close>
lemma total_prob:
  assumes disjoint: "\<forall>i j. i \<noteq> j \<longrightarrow> (B i) \<inter> (B j) = {}"
  assumes fin: "finite I"
  assumes complete: "(\<Union>n \<in> I. (B n)) = \<Omega> ds"
  shows "Pr A ds = (\<Sum>n \<in> I . (Pr_cond A (B n) ds) * (Pr (B n) ds))"
(*<*)
proof -
  show ?thesis sorry
qed
(*>*)

text \<open>Es folgt eine Anwendung des Satzes für Literale Pos s und sein Komplement Neg s\<close>
lemma simp_total :
  shows "Pr A ds = Pr_cond A (mods {Pos s} ds) ds * Pr (mods {Pos s} ds) ds + Pr_cond A (mods {Neg s} ds) ds * Pr (mods {Neg s} ds) ds"
  (*<*)
  using  \<Omega>_def Pr_def Pr_cond_def total_prob compl_sen_union compl_sen_inter
  by (smt (verit) Int_Un_distrib Int_Un_distrib2 Int_Un_eq(1,2,3,4)
      Un_Int_crazy add_divide_distrib boolean_algebra.conj_zero_right
      card_Un_disjoint card_mono compl_sen_inter compl_sen_union
      divide_eq_0_iff fin_mods finite_Int gr0I inf.assoc inf.commute
      inf.left_commute inf_idem inf_le2 inf_right_idem less_numeral_extra(3)
      nat_0_less_mult_iff nonzero_eq_divide_eq of_nat_0_eq_iff of_nat_add
      of_nat_le_0_iff of_nat_mono of_nat_mult)
  (*>*)

text \<open>Die bedingte Wahrscheinlichkeit einer erweiterten Debatte ist gleich der 
bedingten Wahrscheinlichkeit der ursprünglichen Debatte.\<close>
definition jeffrey_cond :: "position set \<Rightarrow> position set \<Rightarrow> ds \<Rightarrow> ds \<Rightarrow> bool"
  where "jeffrey_cond P E ds1 ds2 = (Pr_cond P E (ds1 \<union> ds2) = Pr_cond P E ds1)"

text \<open>Bei uns ist die bedingten Wahrscheinlichkeiten invariant bzgl. der Debattenerweiterung.\<close>
theorem jeffrey_forall [simp]:
  shows "\<forall>E . jeffrey_cond P (mods E (ds1 \<union> ds2)) ds1 ds2" 
  (*<*)
  unfolding jeffrey_cond_def
    Pr_cond_def using Pr_def mods_def subset_of_extended compl_sen_union
  by (smt (verit, best) Int_assoc \<Omega>_def card_0_eq card_gt_0_iff
      divide_divide_eq_right empty_subsetI inf_absorb1 mem_Collect_eq
      nonzero_eq_divide_eq not_empty of_nat_eq_0_iff subsetI)
  (*>*)

text \<open>Wenn die Debatte mit einem unterstützenden Argument (ps, c) erweitert wird, wird der doj des
Literals  nicht kleiner\<close>
theorem direct_supp_weak: 
  shows "doj {c} ds \<le> doj {c} (ds \<union> {(ps, c)})"
proof -
  let ?d0 = "ds"
  let ?d1 = "(ds \<union> {(ps, c)})"
  have "mods {c} ?d1 = mods {c} ?d0" using subset_conclusions subset_of_extended by fast
  moreover have "mods {} ?d1 \<subseteq> mods {} ?d0" using subset_of_extended by blast
  ultimately show ?thesis using omega_inter unfolding Pr_def \<Omega>_def doj_pr
    by (metis (no_types, lifting) card_gt_0_iff card_mono divide_eq_0_iff fin_mods
        frac_le inf_bot_right less_eq_rat_def of_nat_0_le_iff of_nat_0_less_iff
        of_nat_mono)
qed

text \<open>Wenn die Debatte mit einem angreifenden Argument (ps, Neg s) erweitert wird, wird der doj der 
komplementären Konklusion nicht größer\<close>
theorem direct_att_weak:
  shows "doj {Pos s} ds \<ge> doj {Pos s} (ds \<union> {(ps, Neg s)})"
proof -
  have "doj {Pos s} (ds \<union> {(ps, Neg s)}) = 1 - (doj {Neg s} (ds \<union> {(ps, Neg s)}))" 
    using complement_eq_1  by (metis \<Omega>_def \<sigma>_def diff_eq_eq not_empty)
  also have "... \<le> 1 - (doj {Neg s} ds)" using direct_supp_weak  unfolding doj_pr
    using direct_supp_weak doj_pr by force
  also have "... \<le> 1 - (1 - doj {Pos s} ds)" using complement_eq_1
    by (metis \<Omega>_def \<sigma>_def add_diff_cancel_left' dual_order.refl not_empty)
  finally show ?thesis by auto
qed


text \<open>\#TODO Das Hinzuügen von indirekten Argumenten verringert den doj nicht.\<close>
theorem indirectSupport:
  shows "doj {l} ds \<le> doj {l} (ds \<union> {({a}, l), (ps, a)})"
proof -  oops

 

  text \<open>Wenn zwei Debatten (ds1 und ds2) nicht über die gleichen Sätze Aussagen treffen und Position P nur 
Aussagen über ds1 trifft,
dann ist die Anzahl der Modelle der kombinierten Debatte bzgl. P
gleich dem Produkt der Anzahl der Modelle von ds1 bzgl P und der Größe des Grundraums von ds2.\<close>
lemma mods_product:
  assumes "domain_ds ds1 \<inter> domain_ds ds2 = {}"
  assumes "domain_pos P \<inter> domain_ds ds2 = {}"
  shows "card (mods P (ds1 \<union> ds2)) = card (mods P ds1) * card (\<Omega> ds2)" 
(*<*)
proof -
  let ?f = "\<lambda>x :: position . ({l \<in> x. sen l \<in> domain_ds ds1}, {l \<in> x. sen l \<in> domain_ds ds2})"
  have "mods P (ds1 \<union> ds2) = \<Omega> (ds1 \<union> ds2 \<union> (\<Union>p\<in>P. {({}, p)})) " using \<Omega>_def shift_position_into_debate by auto
  moreover have "mods P ds1 = \<Omega> (ds1 \<union> (\<Union>p\<in>P. {({}, p)}))" using \<Omega>_def shift_position_into_debate by auto

  moreover have "bij_betw ?f (\<Omega> (ds1 \<union> ds2 \<union> (\<Union>p\<in>P. {({}, p)}))) 
    (\<Omega> (ds1 \<union> (\<Union>p\<in>P. {({}, p)})) \<times> \<Omega> ds2)" using mods_def coherent_def complete_def consistent_def models_arg.simps
   assms unfolding \<Omega>_def
  proof -
  have empty_univ: "\<forall>L. {La. L \<subseteq> La \<and> La \<Turnstile> UNIV} = {}"
    using coherent_def consistent_def by fastforce
  then show "bij_betw 
      (\<lambda>x. ( {l \<in> x. sen l \<in> domain_ds ds1}, 
             {l \<in> x. sen l \<in> domain_ds ds2})) 
      (mods {} (ds1 \<union> ds2 \<union> (\<Union>p \<in> P. {({}, p)}))) 
      (mods {} (ds1 \<union> (\<Union>p \<in> P. {({}, p)})) \<times> mods {} ds2)"
    by (metis (no_types) \<Omega>_def bot_nat_0.not_eq_extremum 
        card.empty mods_def not_empty)
qed
  ultimately show ?thesis using card_cartesian_product bij_betw_same_card
    by fastforce
qed
(*>*)


text \<open>Daraus folgt direkt, dass das Hinzufügen von komplett unabhängigen Argumenten den doj nicht ändert.\<close>
theorem full_ind:
  assumes "domain_ds ds1 \<inter> domain_ds ds2 = {}"
  assumes "domain_pos P \<inter> domain_ds ds2 = {}"
  shows "doj P ds1 = doj P (ds1 \<union> ds2)"
(*<*)
proof -
  have "card (\<Omega> (ds1 \<union> ds2)) = card (\<Omega> ds1) * card (\<Omega> ds2)"  using \<Omega>_def assms mods_product by auto
  thus ?thesis using mods_product assms unfolding Pr_def omega_inter doj_pr
    using not_empty by auto   
qed
(*>*)

theorem premisses_as_background:
  assumes "doj P (ds \<union> {(ps,c)}) > doj P ds"
  assumes "B \<subseteq> ps" 
  shows "doj_cond P B (ds \<union> {(ps, c)}) \<ge> doj P (ds \<union> {(ps, c)})"
(*<*)
proof -
show ?thesis sorry
qed
(*>*)

(*<*)
theorem reduce_to_relevancy [simp]:
  assumes "\<forall>x \<in> mods {Pos s} ds.  x \<Turnstile> A"
  assumes "\<forall>x \<in> mods {Neg s} ds.  x \<Turnstile> A"

  shows "(Pr B (ds \<union> A) - Pr B (ds)) 
    = ((Pr_cond B (mods {Neg s} ds) ds) - (Pr_cond B (mods {Neg s} ds) ds))
    * ((Pr (mods {Neg s} ds) (ds \<union> A)) - Pr (mods {Neg s} ds) ds)"
proof -
  let ?ps = "mods {Pos s} (ds \<union> A)" 
  let ?ns = "mods {Neg s} (ds \<union> A)"
  let ?d0 = "ds"
  let ?d1 = "ds \<union> A"

  have peq: "?ps = mods {Pos s} ds" and neq: "?ns = mods {Neg s} ds" 
    using assms fullfills_ds_subset subset_of_extended 
    by blast+
 
  have  "(Pr B ?d1 - Pr B ?d0)
=  Pr_cond B ?ps ?d1 * Pr ?ps ?d1 + Pr_cond B ?ns ?d1 * Pr ?ns ?d1
- (Pr_cond B ?ps ?d0 * Pr ?ps ?d0 + Pr_cond B ?ns ?d0 * Pr ?ns ?d0)" 
    using simp_total peq neq  by metis
  also have "...
=  Pr_cond B ?ps ?d0 * Pr ?ps ?d1 + Pr_cond B ?ns ?d0 * Pr ?ns ?d1
- (Pr_cond B ?ps ?d0 * Pr ?ps ?d0 + Pr_cond B ?ns ?d0 * Pr ?ns ?d0)
"  by (metis jeffrey_forall jeffrey_cond_def)
  also have "... 
=  Pr_cond B ?ps ?d0 * Pr ?ps ?d1 + Pr_cond B ?ns ?d0 * (1 - Pr ?ps ?d1)
- (Pr_cond B ?ps ?d0 * Pr ?ps ?d0 + Pr_cond B ?ns ?d0 * (1 - Pr ?ps ?d0))
" using complement_eq_1 doj_pr 
    by (metis \<Omega>_def  \<sigma>_def add_diff_cancel_left' not_empty peq neq)
  also have "... 
= Pr_cond B ?ps ?d0 * (Pr ?ps ?d1 - Pr ?ps ?d0)
 + Pr_cond B ?ns ?d0 * (Pr ?ps ?d1 - Pr ?ps ?d0)"
    by (metis Pr_def \<Omega>_def add.right_neutral cancel_comm_monoid_add_class.diff_cancel compl_sen_union
        mult.commute mult_zero_left neq peq)
  finally show ?thesis
    by (metis Pr_def \<Omega>_def cancel_comm_monoid_add_class.diff_cancel compl_sen_union
        mult_zero_left neq peq)
qed


end
(*>*)





