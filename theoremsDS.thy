theory theoremsDS
  imports Main  "HOL.Rat" defDS
begin


(* Der Begründungsgrad einer beliebigen Position auf der dialektischen Struktur
   ist kleiner gleich 1.
Idee: 
  1. Die Menge aller möglichen koherenten Positionen ist endlich
  2. Die Menge der Positionen, die P erweitern ist eine Teilmenge der Menge aller möglichen
   koherenten Positionen
  3. Aus der Monotonie der Kardinatität folgt, dass "\<sigma> P ds \<le> \<sigma> {} ds"
  \<Rightarrow> doj P ds \<le> 1      
*)
theorem between0_1:
  shows "0 \<le> doj P ds \<and> doj P ds \<le>  1"
proof -

  have subset: "mods P ds \<subseteq> mods {} ds"
    using mods_def by auto
  hence card_le: "\<sigma> P ds \<le> \<sigma> {} ds"
    using fin_mods card_mono \<sigma>_def coherent_extensions_def by metis
  hence lte1: "doj P ds \<le> 1"
    by (metis doj_cond_def doj_def less_divide_eq_1 linorder_not_le of_nat_le_iff
        of_nat_less_0_iff sup_bot.right_neutral)

  have \<sigma>_gt0: "\<forall>Q . \<sigma> Q ds \<ge> 0" using \<sigma>_def card_def by simp
  hence gte0: "doj P ds \<ge> 0" by (simp add: doj_cond_def doj_def)

  show ?thesis using gte0 lte1 by auto
qed

lemma extendedDS_subset:
  shows "mods P (ds \<union> As) \<subseteq> mods P ds"
proof -
  have "\<forall>V . complete V (ds \<union> As) \<longrightarrow> complete V ds"  using complete_def by auto
  have "(ds \<union> As) \<supseteq> ds" by auto
  hence "\<forall>V . consistent V (ds \<union> As) \<longrightarrow> consistent V ds"  using \<open>ds \<subseteq> ds \<union> As\<close> consistent_def by auto
  hence "\<forall>V . complete_consistent V (ds \<union> As) \<longrightarrow> complete_consistent V ds"
    by (metis \<open>\<forall>V. consistent V (ds \<union> As) \<longrightarrow> consistent V ds\<close> \<open>\<forall>V. complete V (ds \<union> As) \<longrightarrow> complete V ds\<close> complete_consistent_def)
   hence "\<forall>V . V \<Turnstile> (ds \<union> As) \<longrightarrow> V \<Turnstile> ds" using coherent_def by simp

   thus ?thesis using mods_def
     unfolding mods_def by blast
 qed

(* 
komplementärer Satz := Belegt den gleichen Satz unterschiedlich
Die Vereinigung alle Modelle von komplementären Sätzen ist die Menge aller Möglichen Modelle.
*)
lemma compl_sen_union:
  "mods {Pos s} ds \<union> mods {Neg s} ds = mods {} ds"
proof 
  show "mods {Pos s} ds \<union> mods {Neg s} ds \<subseteq> mods {} ds"
    by (simp add: Collect_mono mods_def)
next 
  show "mods {} ds \<subseteq> mods {Pos s} ds \<union> mods {Neg s} ds"
  proof 
    fix V 
    assume "V \<in> mods {} ds"

    have "V \<in> mods {Pos s} ds \<or> V \<in> mods {Neg s} ds"
      by (metis (lifting) \<open>V \<in> mods {} ds\<close> coherent_def
          mods_def complete_consistent_def complete_def insert_subset
          literal.exhaust_sel mem_Collect_eq)
    thus "V \<in> mods {Pos s} ds \<union> mods {Neg s} ds" 
      by auto
  qed
qed


(* Die Modelle komplementären Sätzen überschneiden sich nicht *)
lemma compl_sen_inter:
"mods {Pos s} ds \<inter> mods {Neg s} ds = {}"
proof
  show "{} \<subseteq> mods {Pos s} ds \<inter> mods {Neg s} ds"
    by simp
next
  show "mods {Pos s} ds \<inter> mods {Neg s} ds \<subseteq> {}"
  proof
  fix V
  assume "V \<in> mods {Pos s} ds \<inter> mods {Neg s} ds"
  hence hpos: "V \<in> mods {Pos s} ds" 
    and hneg: "V \<in> mods {Neg s} ds" by auto
  have 1: "V \<notin> mods {Neg s} ds" 
    using hpos coherent_def mods_def
          complete_consistent_def consistent_def by auto
  thus "V \<in> {}" using hneg by contradiction
    qed
  qed

theorem complement_eq_1:
  assumes "\<sigma> {} ds > 0"
  shows "doj {Pos s} ds + doj {Neg s} ds = 1"
proof - 
  have "1  = doj {} ds"  by (simp add: assms doj_cond_def doj_def)
  also have "... = (((rat_of_nat(\<sigma> {} ds))) / (rat_of_nat (\<sigma> {} ds)))" 
    using doj_cond_def doj_def assms calculation by simp
  also have "... = (((rat_of_nat(\<sigma> {Pos s} ds + \<sigma> {Neg s} ds))) / (rat_of_nat (\<sigma> {} ds)))"
    using compl_sen_inter compl_sen_union by (metis \<sigma>_def card_Un_disjoint coherent_extensions_def
      fin_mods) 
  also have "... = doj {Pos s} ds + doj {Neg s} ds" 
    by (metis add_divide_distrib doj_cond_def doj_def insert_is_Un of_nat_add)
  finally show ?thesis by simp
qed


(*
Wenn es in der ds, die mit dem Argument ({a},p) erweitert wurde, eine koherente Position gibt,
hat die Aussage p in dieser ds einen größer-gleichen doj, als die Aussage p in der ds ohne dem Argument.
*)
theorem directSupport:
  assumes sat: "\<sigma> {} ds > 0"
  shows "doj {l} ds \<le> doj {l} (ds \<union> {({a}, l)})"
proof -

  have "mods {} (ds \<union> {({a}, l)}) \<subseteq> mods {} ds" 
    using extendedDS_subset by blast
  hence nenner: "\<sigma> {} ds \<ge> \<sigma> {} (ds \<union> {({a}, l)})"
     using \<sigma>_def card_mono by (metis fin_mods)


   have "\<forall>V :: position . V \<supseteq> {l} \<longrightarrow> (V  \<Turnstile> ds \<longrightarrow> V \<Turnstile> (ds \<union> {({a}, l)}))" 
     by (simp add: coherent_def complete_consistent_def complete_def consistent_def)

   hence  "mods {l} (ds \<union> {({a}, l)}) \<supseteq> mods {l} ds"
     using coherent_def  unfolding mods_def
     by blast
   hence "mods {l} (ds \<union> {({a}, l)}) =  mods {l} ds"
     using extendedDS_subset by blast
   hence zaehler: "\<sigma> {l} ds = \<sigma> {l} (ds \<union> {({a}, l)})"
     using \<sigma>_def by presburger
    

   show ?thesis using zaehler nenner doj_cond_def doj_def \<sigma>_def fin_mods 
     unfolding doj_def doj_cond_def
   (* Sledgehammer *)
   proof -
     have f1: "card {L. {} \<subseteq> L \<and> L \<Turnstile> (ds \<union> {({a}, l)})} \<le> card {L. {} \<subseteq> L \<and> L \<Turnstile> ds}"
       using \<sigma>_def mods_def nenner by presburger
     have f2: "\<forall>L. finite (L::literal set set)"
       by (meson Finite_Set.finite_set finite_positions rev_finite_subset subset_UNIV)
     then have "(\<exists>L. {La. L \<subseteq> La \<and> La \<Turnstile> (ds \<union> {({a}, l)})} \<noteq> {}) \<or> rat_of_nat (card {L. {l} \<subseteq> L \<and> L \<Turnstile> ds}) / rat_of_nat (card {L. {} \<subseteq> L \<and> L \<Turnstile> ds}) \<le> rat_of_nat (card {L. {l} \<subseteq> L \<and> L \<Turnstile> ds}) / rat_of_nat (card {L. {} \<subseteq> L \<and> L \<Turnstile> (ds \<union> {({a}, l)})})"
       using \<sigma>_def mods_def less_eq_rat_def zaehler by auto
     moreover
     { assume "\<exists>L. {La. L \<subseteq> La \<and> La \<Turnstile> (ds \<union> {({a}, l)})} \<noteq> {}"
       then have "{L. {} \<subseteq> L \<and> L \<Turnstile> (ds \<union> {({a}, l)})} \<noteq> {}"
         by blast
       then have "rat_of_nat (card {L. {l} \<subseteq> L \<and> L \<Turnstile> ds}) / rat_of_nat (card {L. {} \<subseteq> L \<and> L \<Turnstile> ds}) \<le> rat_of_nat (card {L. {l} \<subseteq> L \<and> L \<Turnstile> ds}) / rat_of_nat (card {L. {} \<subseteq> L \<and> L \<Turnstile> (ds \<union> {({a}, l)})})"
         using f2 f1 by (metis (lifting) card_0_eq divide_mono less_eq_rat_def of_nat_0_le_iff of_nat_eq_0_iff of_nat_le_iff) }
     ultimately show "rat_of_nat (\<sigma> ({l} \<union> {}) ds) / rat_of_nat (\<sigma> {} ds) \<le> rat_of_nat (\<sigma> ({l} \<union> {}) (ds \<union> {({a}, l)})) / rat_of_nat (\<sigma> {} (ds \<union> {({a}, l)}))"
       using \<sigma>_def mods_def zaehler by auto
   qed 
 qed


(*
Wenn es in der ds, die mit dem angreifenden Argument ({a}, Neg p) erweitert wurde, eine koherente Position gibt,
hat die Aussage Pos p in dieser ds einen kleinier-gleichen doj, als die Aussage Pos p in der ds ohne dem Argument.
*)
theorem directAtteck:
  assumes sat: "\<sigma> {} (ds \<union> {({a}, Neg s)}) > 0"
  shows "doj {Pos s} ds \<ge> doj {Pos s} (ds \<union> {({a}, Neg s)})"
proof -
  have "doj {Pos s} (ds \<union> {({a}, Neg s)}) = 1 - (doj {Neg s} (ds \<union> {({a}, Neg s)}))" 
    using complement_eq_1  by (metis add_diff_cancel_right' sat)
  also have "... \<le> 1 - (doj {Neg s} ds)" using directSupport 
    by (metis between0_1 diff_left_mono div_by_0 doj_cond_def doj_def gr0I of_nat_0)
  also have "... \<le> 1 - (1 - doj {Pos s} ds)" using complement_eq_1
    by (metis \<sigma>_def add_diff_cancel_left' card_mono extendedDS_subset fin_mods
        gr0I linorder_not_le nle_le sat)
  finally show ?thesis by auto
qed


(*
Wenn ein tautologisches Argument (Konklusion ist Teil der Prämisse)
hinzugefügt wird, ändert sich der doj einer beliebigen Position nicht. 
*)
theorem addTaut:
  assumes taut: "c \<in> ps"
  shows "doj P ds = doj P (ds \<union> {(ps, c)})"
proof -
  have "mods {} (ds \<union> {(ps, c)}) \<supseteq> mods {} ds" 
    using taut coherent_def mods_def complete_consistent_def complete_def consistent_def by fastforce
  hence nenner: "\<sigma> {} ds =  \<sigma> {} (ds \<union> {(ps, c)})" using extendedDS_subset \<sigma>_def 
    by (metis subset_antisym)

  have "\<forall>V :: position . V \<supseteq> P \<longrightarrow> (V  \<Turnstile> ds \<longrightarrow> V \<Turnstile> (ds \<union> {(ps, c)}))"  
    using coherent_def complete_consistent_def complete_def consistent_def taut by force
   hence  "mods P (ds \<union> {(ps, c)}) \<supseteq> mods P ds"
     using coherent_def  unfolding mods_def
     by blast
   hence "mods P (ds \<union> {(ps, c)}) = mods P ds" using extendedDS_subset 
     by blast
  thus ?thesis using nenner
    by (simp add: \<sigma>_def doj_cond_def doj_def)
qed



lemma twice_extended_doj_bigger:
  assumes sat: "\<sigma> {} (ds \<union> {({a}, l), (ps, a)}) > 0"
  shows "doj {l} (ds \<union> {({a}, l)}) \<le> doj {l} (ds \<union> {({a}, l), (ps, a)})"
proof - 
  have "mods {} (ds \<union> {({a}, l), (ps, a)}) \<subseteq> mods {} (ds \<union> {({a}, l)})" 
    using extendedDS_subset 
      by (metis Un_insert_left Un_insert_right boolean_algebra_cancel.sup0)
  hence nenner: "\<sigma> {} (ds \<union> {({a}, l)})  \<ge> \<sigma> {} (ds \<union> {({a}, l), (ps, a)})"
     using \<sigma>_def card_mono by (metis fin_mods)

   have   "mods {l} (ds \<union> {({a}, l)}) \<subseteq> mods {l} (ds \<union> {({a}, l), (ps, a)})" 
   proof -
     have "\<forall>V :: position . V \<supseteq> {l} \<and> models_arg V (ps, a) \<longrightarrow>
         (V  \<Turnstile> (ds \<union> {({a}, l)}) \<longrightarrow> V \<Turnstile>(ds \<union> {({a}, l), (ps, a)}))" 
     using  coherent_def complete_consistent_def complete_def consistent_def
     by simp
     show ?thesis sorry
     qed
   hence "mods {l} (ds \<union> {({a}, l)}) = mods {l} (ds \<union> {({a}, l), (ps, a)})" using extendedDS_subset
     by (metis Un_insert_left Un_insert_right boolean_algebra_cancel.sup0 subset_antisym)
     
   thus  ?thesis using nenner
     by (metis \<open>mods {l} (ds \<union> {({a}, l)}) \<subseteq> mods {l} (ds \<union> {({a}, l), (ps, a)})\<close> \<sigma>_def card_mono
         divide_mono doj_cond_def doj_def fin_mods insert_is_Un of_nat_0_le_iff of_nat_0_less_iff of_nat_mono
         sat) 
 qed

(*
Wenn es in der ds, die mit dem Argument ({a},p) erweitert wurde, eine koherente Position gibt,
hat die Aussage p in dieser ds einen größer-gleichen doj, als die Aussage p in der ds ohne dem Argument.
*)
theorem indirectSupport:
  assumes sat: "\<sigma> {} (ds \<union> {({a}, l), (ps, a)}) > 0"
  shows "doj {l} ds \<le> doj {l} (ds \<union> {({a}, l), (ps, a)})"
proof -
  have "doj {} ds > 0" using sat
    by (metis \<sigma>_def between0_1 boolean_algebra_cancel.sup0 card_mono divide_eq_0_iff doj_cond_def doj_def
        extendedDS_subset fin_mods linorder_not_le of_nat_eq_0_iff order_less_le)
  hence "doj {l} ds \<le> doj {l} (ds \<union> {({a}, l)})" using directSupport 
    by (metis div_by_0 doj_cond_def doj_def dual_order.refl gr0I linorder_not_le of_nat_0)
  also have "... \<le>  doj {l} (ds \<union> {({a}, l), (ps, a)})" using sat twice_extended_doj_bigger
    by blast 
  finally show ?thesis by auto
qed

(*
Wenn ein unabhängiges Argument (Konklusion und Prämissen kommen in ds nicht vor)
hinzugefügt wird, ändert sich der doj einer beliebigen Position nicht. 

nitpick findet ein Gegenbeispiel. Ich kann das aber noch nicht ganz nachvollziehen. 
Kann ich mit "value" \<sigma> berechnen?
*)

theorem addInd:
  assumes full_indepentent: "\<forall>(PS, C) \<in> ds . sen c \<notin> image sen PS \<and> sen c \<noteq> sen C \<and> (\<forall>p \<in> ps . sen p \<notin> image sen PS \<and> sen p \<noteq> sen C)"
  assumes new_arg_not_inP: "\<forall>p \<in> ps . sen p \<notin> image sen P \<and> sen c \<notin> image sen P"
  assumes "ds \<noteq> {}"
  assumes "P \<noteq> {}"
  shows "doj P ds = doj P (ds \<union> {(ps, c)})"
proof -
  have "mods P ds = mods P (ds \<union> {(ps, c)})"
    using full_indepentent new_arg_not_inP coherent_def nitpick [user_axioms = true] sorry
  thus ?thesis unfolding doj_cond_def
    using \<sigma>_def sorry
 qed


end
