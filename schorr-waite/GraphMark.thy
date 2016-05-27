theory GraphMark
imports "~/verification/mainline/l4v/tools/autocorres/AutoCorres"
begin

install_C_file "graph_mark.c"
autocorres [heap_abs_syntax] "graph_mark.c"

context graph_mark begin

-- "Specification"

type_synonym mark = "32 word"
type_synonym state_pred = "lifted_globals \<Rightarrow> bool"

definition out :: "lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr set" where
  "out s p \<equiv> { s[p]\<rightarrow>left, s[p]\<rightarrow>right }"

inductive_set reach :: "lifted_globals \<Rightarrow> node_C ptr set \<Rightarrow> node_C ptr set"
  for s :: lifted_globals and R :: "node_C ptr set"
  where
    reach_root: "p \<in> R \<Longrightarrow> p \<noteq> NULL \<Longrightarrow> p \<in> reach s R"
  | reach_step: "p \<in> reach s R \<Longrightarrow> q \<in> out s p \<Longrightarrow> q \<noteq> NULL \<Longrightarrow> q \<in> reach s R"

definition mark :: "mark \<Rightarrow> bool \<Rightarrow> node_C \<Rightarrow> node_C" where
  "mark m c node \<equiv> if c then node \<lparr> mark_C := m \<rparr> else node"

definition mark_set :: "mark \<Rightarrow> node_C ptr set \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals" where
  "mark_set m R s \<equiv> heap_node_C_update (\<lambda> h p. mark m (p \<in> R) (h p)) s"

definition mark_precondition :: "state_pred \<Rightarrow> node_C ptr \<Rightarrow> state_pred" where
  "mark_precondition P root \<equiv> \<lambda> s. let R = reach s {root} in
    (\<forall> p \<in> R. is_valid_node_C s p \<and> s[p]\<rightarrow>mark = 0) \<and> P (mark_set 3 R s)"

definition mark_specification :: "state_pred \<Rightarrow> node_C ptr \<Rightarrow> bool" where
  "mark_specification P root \<equiv> \<lbrace> mark_precondition P root \<rbrace> graph_mark' root \<lbrace> \<lambda> _. P \<rbrace>!"

-- "Proof"

definition mark_incr :: "node_C ptr \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals" where
  "mark_incr p \<equiv> heap_node_C_update (\<lambda> h. h(p := mark_C_update (\<lambda> m. m + 1) (h p)))"

lemma mark_incr_mark [simp]: "(mark_incr q s)[p]\<rightarrow>mark = s[p]\<rightarrow>mark + (if p = q then 1 else 0)"
  unfolding mark_incr_def by (simp add: fun_upd_def graph_mark.get_node_mark_def)

end

locale link_read_stable =
  fixes
    f :: "lifted_globals \<Rightarrow> lifted_globals"
  assumes
    read_stable_l [simp]: "\<And> p. (f s)[p]\<rightarrow>left = s[p]\<rightarrow>left" and
    read_stable_r [simp]: "\<And> p. (f s)[p]\<rightarrow>right = s[p]\<rightarrow>right" and
    read_stable_v [simp]: "\<And> p. is_valid_node_C (f s) p = is_valid_node_C s p"

context link_read_stable begin

sublocale graph_mark .

lemma out_link_read_stable [simp]: "out (f s) = out s"
  unfolding out_def[abs_def] by fastforce

lemma reach_link_read_stable [simp]: "reach (f s) R = reach s R"
  proof -
    { fix p assume "p \<in> reach (f s) R" hence "p \<in> reach s R"
      by (induction rule: reach.induct) (auto intro: reach.intros) }
    moreover
    { fix p assume "p \<in> reach s R" hence "p \<in> reach (f s) R"
      by (induction rule: reach.induct) (auto intro: reach.intros) }
    ultimately
    show ?thesis by blast
  qed

end

context graph_mark begin

sublocale mark_incr_link_read_stable?: link_read_stable "mark_incr q"
  apply unfold_locales
  by (auto simp: mark_incr_def fun_upd_def
                 graph_mark.get_node_left_def graph_mark.get_node_right_def)

sublocale mark_set_link_read_stable?: link_read_stable "mark_set m R"
  apply unfold_locales
  by (auto simp: mark_set_def mark_def fun_upd_def
                 graph_mark.get_node_left_def graph_mark.get_node_right_def)

lemma mark_incr_left_upd [simp]:"(mark_incr q s)[p\<rightarrow>left := v] = mark_incr q s[p\<rightarrow>left := v]"
  unfolding mark_incr_def
  by (smt fun_upd_def fun_upd_twist fun_upd_upd graph_mark.update_node_left_def
          lifted_globals.surjective lifted_globals.update_convs(5) node_C_updupd_diff(2))

lemma mark_incr_right_upd [simp]:"(mark_incr q s)[p\<rightarrow>right := v] = mark_incr q s[p\<rightarrow>right := v]"
  unfolding mark_incr_def
  by (smt fun_upd_def fun_upd_twist fun_upd_upd graph_mark.update_node_right_def
          lifted_globals.surjective lifted_globals.update_convs(5) node_C_updupd_diff(1))

lemma reach_subset: assumes "R \<subseteq> S" shows "reach s R \<subseteq> reach s S"
  proof -
    { fix p have "p \<in> reach s R \<Longrightarrow> R \<subseteq> S \<Longrightarrow> p \<in> reach s S"
      by (induction rule: reach.induct) (auto intro: reach.intros) }
    thus ?thesis using assms by auto
  qed

lemma reach_incl: "NULL \<notin> R \<Longrightarrow> R \<subseteq> reach s R"
  by (auto intro: reach.intros)

lemma reachable_null [simp]: "reach s {NULL} = {}"
  proof -
    { fix p have "p \<in> reach s {NULL} \<Longrightarrow> False" by (induction rule: reach.induct) auto }
    thus ?thesis by auto
  qed

lemma reach_incl_null: assumes "R' = insert NULL R" shows "reach s R' = reach s R"
  proof -
    { fix p assume "p \<in> reach s R'" "R' = insert NULL R" hence "p \<in> reach s R"
      by (induction rule: reach.induct) (auto intro: reach.intros) }
    moreover
    { fix p assume "p \<in> reach s R" "R' = insert NULL R" hence "p \<in> reach s R'"
      by (induction rule: reach.induct) (auto intro: reach.intros) }
    ultimately
    show ?thesis using assms by blast
  qed

lemma reachable_empty [simp]: "reach s {} = {}"
  by (metis empty_subsetI reach_subset reachable_null subset_antisym)

lemma mark_set_empty [simp]: "mark_set m {} u = u"
  unfolding mark_set_def mark_def by simp

lemma mark_incr_p_mark_q [simp]: "q \<noteq> p \<Longrightarrow> (mark_incr p s)[q]\<rightarrow>mark = s[q]\<rightarrow>mark"
  by (simp add: fun_upd_def graph_mark.get_node_mark_def mark_incr_def)

lemma reach_rotate:
  assumes
    P: "p \<noteq> NULL" and
    R: "R = {s[p]\<rightarrow>left, p}"
  shows
    "reach s[p\<rightarrow>left := s[p]\<rightarrow>right][p\<rightarrow>right := q] R = reach s {p,q}"
  proof -
    {
      fix r
      assume "r \<in> reach s[p\<rightarrow>left := s[p]\<rightarrow>right][p\<rightarrow>right := q] {s[p]\<rightarrow>left, p}"
      hence "r \<in> reach s {p,q}"
      proof (induction rule: reach.induct)
        case reach_root thus ?case
        using assms out_def reach.intros by blast
      next
        case reach_step thus ?case
        by (metis fun_upd_other fun_upd_same graph_mark.heap_abs_simps(12,14,22,24)
                  out_def reach.intros insertCI insertE)
      qed
    }
    moreover
    {
      fix r
      assume "r \<in> reach s {p,q}"
      hence "r \<in> reach s[p\<rightarrow>left := s[p]\<rightarrow>right][p\<rightarrow>right := q] {s[p]\<rightarrow>left, p}"
      proof (induction rule: reach.induct)
        case (reach_root r')
        show ?case
        proof (cases "r' = p")
          case True show ?thesis
          using reach_root True reach.reach_root by auto
        next
          case False
          have Q: "r' = q" "q \<noteq> NULL" using False reach_root by auto
          show ?thesis
          by (rule reach_step[of p])
             (auto simp: Q P out_def fun_upd_same intro: reach.intros)
        qed
      next
        case reach_step show ?case using reach_step P
        by (metis fun_upd_other fun_upd_same graph_mark.heap_abs_simps(12,14,22,24)
                  out_def empty_iff insertE insert_subset order_refl reach.intros)
      qed
    }
    ultimately show ?thesis using R by blast
  qed

lemma reach_rotate_left [simp]:
  "p \<noteq> NULL \<Longrightarrow> reach s[p\<rightarrow>left := s[p]\<rightarrow>right][p\<rightarrow>right := q] {s[p]\<rightarrow>left,p} = reach s {p,q}"
  "p \<noteq> NULL \<Longrightarrow> reach s[p\<rightarrow>left := s[p]\<rightarrow>right][p\<rightarrow>right := q] {p,s[p]\<rightarrow>left} = reach s {p,q}"
  by (rule reach_rotate; auto)+

lemma reach_rotate_id [simp]:
  assumes "s[p]\<rightarrow>left = p" "p \<noteq> NULL"
  shows "reach s[p\<rightarrow>left := s[p]\<rightarrow>right][p\<rightarrow>right := q] {p} = reach s {p,q}"
  by (rule reach_rotate) (auto simp: assms)

lemma reach_rotate_null [simp]:
  assumes
    "p \<noteq> NULL" "s[p]\<rightarrow>left = NULL"
  shows
    "reach s[p\<rightarrow>left := s[p]\<rightarrow>right][p\<rightarrow>right := q] {p,NULL} = reach s {p,q}"
    "reach s[p\<rightarrow>left := s[p]\<rightarrow>right][p\<rightarrow>right := q] {NULL,p} = reach s {p,q}"
  by (rule reach_rotate; auto simp: assms)+

lemma setsum_extract_reach:
  "p \<noteq> NULL \<Longrightarrow> (\<Sum> p \<in> reach s {p,q}. f p) = f p + (\<Sum> p \<in> reach s {p,q} - {p}. f p)"
  by (auto simp: reach_root setsum.remove)

lemma reach_left:
  "s[p]\<rightarrow>left \<noteq> NULL \<Longrightarrow> p \<noteq> NULL \<Longrightarrow> s[p]\<rightarrow>left \<in> reach s {p,q}"
  using out_def reach_root reach_step by blast

abbreviation copy_node :: "node_C ptr \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals \<Rightarrow> lifted_globals" where
  "copy_node p m \<equiv> heap_node_C_update (\<lambda> h. h (p := heap_node_C m p))"

abbreviation cmp_links :: "node_C ptr \<Rightarrow> lifted_globals \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<Rightarrow> bool" where
  "cmp_links p m l r \<equiv> l = m[p]\<rightarrow>left \<and> r = m[p]\<rightarrow>right"

type_synonym path_ok_t =
  "lifted_globals \<Rightarrow> lifted_globals \<Rightarrow> node_C ptr set
    \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr list \<Rightarrow> bool"

primrec tail_ok :: path_ok_t where
  "tail_ok s m M r q p []        = (p = NULL \<and> q = r \<and> s = m)" |
  "tail_ok s m M r q p (p' # ps) = (p = p' \<and>
     (s[p]\<rightarrow>mark = 1 \<and>
        cmp_links p m q s[p]\<rightarrow>left \<and>
        tail_ok (copy_node p m s) m M r p s[p]\<rightarrow>right ps \<or>
      s[p]\<rightarrow>mark = 2 \<and>
        m[p]\<rightarrow>left \<in> M \<and>
        cmp_links p m s[p]\<rightarrow>right q \<and>
        tail_ok (copy_node p m s) m M r p s[p]\<rightarrow>left ps))"

primrec path_ok :: path_ok_t where
  "path_ok s m M r q p []        = (p = NULL \<and> q = r \<and> (r = NULL \<or> r \<in> M) \<and> s = m)" |
  "path_ok s m M r q p (p' # ps) = (p = p' \<and>
     (s[p]\<rightarrow>mark = 0 \<and>
        cmp_links p m s[p]\<rightarrow>left s[p]\<rightarrow>right \<and>
        tail_ok (copy_node p m s) m M r p q ps \<or>
      s[p]\<rightarrow>mark = 1 \<and>
        m[p]\<rightarrow>left \<in> M \<and>
        cmp_links p m q s[p]\<rightarrow>left \<and>
        tail_ok (copy_node p m s) m M r p s[p]\<rightarrow>right ps \<or>
      s[p]\<rightarrow>mark = 2 \<and>
        {m[p]\<rightarrow>left, m[p]\<rightarrow>right} \<subseteq> M \<and>
        cmp_links p m s[p]\<rightarrow>right q \<and>
        tail_ok (copy_node p m s) m M r p s[p]\<rightarrow>left ps))"

primrec mark_invariant :: "state_pred \<Rightarrow> node_C ptr \<Rightarrow> node_C ptr \<times> node_C ptr \<Rightarrow> state_pred" where
  "mark_invariant P root (p,q) s =
    (\<exists> path F m.
      let
        R = reach m {root};
        M = F \<union> set path;
        U = R - F;
        Z = R - M;
        t = mark_set 3 U m
      in
        P t \<and>
        set path \<subseteq> R \<and>
        F \<subseteq> R \<and>
        reach t F = F \<and>
        R = reach s {p,q} \<and>
        path_ok s m M root q p path \<and>
        (\<forall> p \<in> R. is_valid_node_C s p) \<and>
        (\<forall> p \<in> Z. s[p]\<rightarrow>mark = 0) \<and>
        (\<forall> p \<in> F. s[p]\<rightarrow>mark = 3))"

fun mark_measure :: "(node_C ptr \<times> node_C ptr) \<times> lifted_globals \<Rightarrow> nat" where
  "mark_measure ((p,q),s) = setsum (\<lambda> p. 3 - unat s[p]\<rightarrow>mark) (reach s {p,q})"

lemma null_path_empty:
  assumes
    "path_ok s m M root q NULL path"
    "set path \<subseteq> reach t roots"
  shows
    "path = []"
  using assms by (cases path; auto elim: reach.cases)

lemma mark_incr_replace [simp]:
  "heap_node_C_update (\<lambda> h. h (p := heap_node_C m p)) (mark_incr p s) =
   heap_node_C_update (\<lambda> h. h (p := heap_node_C m p)) s"
  by (simp add: mark_incr_def)

lemma set_left_replace [simp]:
  "heap_node_C_update (\<lambda> h. h (p := heap_node_C m p)) s[p\<rightarrow>left := q] =
   heap_node_C_update (\<lambda> h. h (p := heap_node_C m p)) s"
  by (simp add: graph_mark.update_node_left_def)

lemma set_right_replace [simp]:
  "heap_node_C_update (\<lambda> h. h (p := heap_node_C m p)) s[p\<rightarrow>right := q] =
   heap_node_C_update (\<lambda> h. h (p := heap_node_C m p)) s"
  by (simp add: graph_mark.update_node_right_def)

lemma graph_mark'_correct: "mark_specification P root"
  unfolding
    mark_specification_def mark_precondition_def graph_mark'_def
    whileLoop_add_inv[where I="mark_invariant P root" and M="mark_measure"]
    mark_incr_def[symmetric]
  apply (wp; clarsimp)
  subgoal for p q s path F m
   apply (cases path; clarsimp simp: Let_def)
   subgoal for ps
    apply (subst setsum_extract_reach[of p]; clarsimp)+
    apply (cases "s[p]\<rightarrow>left = p";
           cases "s[p]\<rightarrow>left = NULL";
           cases "s[s[p]\<rightarrow>left]\<rightarrow>mark = 0";
           (frule (1) reach_left[where q = q])?;
           elim disjE; clarsimp)
    apply (rule exI[where x=path]; rule exI[where x=F]; rule exI[where x=m];
           clarsimp simp: fun_upd_same)
    sorry
   done
  subgoal for q s path F m
   apply (clarsimp simp: Let_def)
   apply (frule (1) null_path_empty)
   apply (clarsimp)
   apply (cases "root = NULL"; clarsimp)
   apply (frule reach_subset[of "{root}" F m, simplified])
   by auto
  subgoal for s
   apply (rule exI[where x="if root = NULL then [] else [root]"];
          rule exI[where x="{}"]; rule exI[where x=s])
   apply (cases "root = NULL";
          simp add: Let_def reach_incl[of "{root}", simplified])
   apply (subst reach_incl_null[of "{root,NULL}"])
   by auto
  done

end

end
