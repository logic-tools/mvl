(*

Formalization of Many-Valued Logics - Isabelle Partiality.thy

Anders Schlichtkrull & Jørgen Villadsen, DTU Compute, Denmark

*)

theory Partiality imports Main begin

section \<open>Syntax and Semantics\<close>

text \<open>Syntax of propositional logic with strings as identifiers in atomic formulas\<close>

type_synonym id = string

datatype fm = Pro id | Truth | Neg' fm | Con fm fm | Eql fm fm | Eql' fm fm

text \<open>Semantics of propositional logic with determinate and indeterminate truth values\<close>

datatype tv = Det bool | is_indet: Indet (get_indet: nat)

abbreviation (input)
  "eval_neg p \<equiv>
    (
      case p of
        Det False \<Rightarrow> Det True |
        Det True \<Rightarrow> Det False |
        Indet n \<Rightarrow> Indet n
    )"

fun
  eval :: "(id \<Rightarrow> tv) \<Rightarrow> fm \<Rightarrow> tv"
where
  "eval i (Pro s) = i s" |
  "eval i Truth = Det True" |
  "eval i (Neg' p) = eval_neg (eval i p)" |
  "eval i (Con p q) =
    (
      if eval i p = eval i q then eval i p else
      if eval i p = Det True then eval i q else
      if eval i q = Det True then eval i p else Det False
    )" |
  "eval i (Eql p q) =
    (
      if eval i p = eval i q then Det True else Det False
    )" |
  "eval i (Eql' p q) =
    (
      if eval i p = eval i q then Det True else
        (
          case (eval i p, eval i q) of
            (Det True, _) \<Rightarrow> eval i q |
            (_, Det True) \<Rightarrow> eval i p |
            (Det False, _) \<Rightarrow> eval_neg (eval i q) |
            (_, Det False) \<Rightarrow> eval_neg (eval i p) |
            _ \<Rightarrow> Det False
        )
    )"

text \<open>Proofs of key properties\<close>

proposition "eval i (Eql p q) = Det (eval i p = eval i q)"
  by simp

theorem eval_negation:
  "eval i (Neg' p) =
    (
      if eval i p = Det False then Det True else
      if eval i p = Det True then Det False else
      eval i p
    )"
  by (cases "eval i p") simp_all

theorem eval_equality:
  "eval i (Eql' p q) =
    (
      if eval i p = eval i q then Det True else
      if eval i p = Det True then eval i q else
      if eval i q = Det True then eval i p else
      if eval i p = Det False then eval i (Neg' q) else
      if eval i q = Det False then eval i (Neg' p) else
      Det False
    )"
  by (cases "eval i p"; cases "eval i q") simp_all

text \<open>Additional operators\<close>

abbreviation "Falsity \<equiv> Neg' Truth"

abbreviation "Dis p q \<equiv> Neg' (Con (Neg' p) (Neg' q))"

abbreviation "Imp p q \<equiv> Eql p (Con p q)"

abbreviation "Imp' p q \<equiv> Eql' p (Con p q)"

abbreviation "Box p \<equiv> (Eql p Truth)"

abbreviation "Neg p \<equiv> Neg' (Box p)"

text \<open>Validity\<close>

definition
  valid :: "fm \<Rightarrow> bool"
where
  "valid p \<equiv> \<forall>i. eval i p = Det True"

text \<open>Key equalities\<close>

proposition "valid (Eql p (Neg' (Neg' p)))"
  unfolding valid_def
  using eval_negation
  by simp

proposition "valid (Eql Truth (Neg' Falsity))"
  unfolding valid_def
  by simp

proposition "valid (Eql Falsity (Neg' Truth))"
  unfolding valid_def
  by simp

proposition "valid (Eql p (Con p p))"
  unfolding valid_def
  by simp

proposition "valid (Eql p (Con Truth p))"
  unfolding valid_def
  by simp

proposition "valid (Eql p (Con p Truth))"
  unfolding valid_def
  by simp

proposition "valid (Eql Truth (Eql' p p))"
  unfolding valid_def
  by simp

proposition "valid (Eql p (Eql' Truth p))"
  unfolding valid_def
  by simp

proposition "valid (Eql p (Eql' p Truth))"
  unfolding valid_def
proof
  fix i
  show "eval i (Eql p (Eql' p Truth)) = Det True"
    by (cases "eval i p") simp_all
qed

proposition "valid (Eql (Neg' p) (Eql' Falsity p))"
  unfolding valid_def
proof
  fix i
  show "eval i (Eql (Neg' p) (Eql' (Neg' Truth) p)) = Det True"
    by (cases "eval i p") simp_all
qed

proposition "valid (Eql (Neg' p) (Eql' p Falsity))"
  unfolding valid_def
  using eval.simps eval_equality eval_negation
  by metis

text \<open>Selected theorems\<close>

theorem double_negation: "valid (Neg' (Neg' p)) \<longleftrightarrow> valid p"
  unfolding valid_def
  using eval_negation
  by auto

theorem conjunction: "valid (Con p q) \<longleftrightarrow> valid p \<and> valid q"
  unfolding valid_def
  by auto

corollary "valid (Con p q) \<Longrightarrow> valid p"
  using conjunction
  by simp

corollary "valid (Con p q) \<Longrightarrow> valid q"
  using conjunction
  by simp

proposition "valid p \<Longrightarrow> valid (Imp p q) \<Longrightarrow> valid q"
  unfolding valid_def
  using eval.simps tv.inject
  by (metis (full_types))

proposition "valid p \<Longrightarrow> valid (Imp' p q) \<Longrightarrow> valid q"
  unfolding valid_def
  using eval.simps eval_equality
  by (metis (full_types))

section \<open>Truth Tables\<close>

definition
  tv_pair_row :: "tv list \<Rightarrow> tv \<Rightarrow> (tv * tv) list"
where
  "tv_pair_row tvs tv = map (\<lambda>x. (tv, x)) tvs"

definition
  tv_pair_table :: "tv list \<Rightarrow> (tv * tv) list list"
where
  "tv_pair_table tvs \<equiv> map (tv_pair_row tvs) tvs"

definition
  map_row :: "(tv \<Rightarrow> tv \<Rightarrow> tv) \<Rightarrow> (tv * tv) list \<Rightarrow> tv list"
where
  "map_row f tvtvs = map (\<lambda>(x,y). f x y) tvtvs"

definition
  map_table :: "(tv \<Rightarrow> tv \<Rightarrow> tv) \<Rightarrow> (tv * tv) list list \<Rightarrow> tv list list"
where
  "map_table f tvtvss = map (map_row f) tvtvss"

definition
  unary_truth_table :: "fm \<Rightarrow> tv list \<Rightarrow> tv list"
where
  "unary_truth_table p tvs =
      map (\<lambda>x. eval ((\<lambda>x. Det undefined)(''p'' := x)) p) tvs"

definition
  binary_truth_table :: "fm \<Rightarrow> tv list \<Rightarrow> tv list list"
where
  "binary_truth_table p tvs =
      map_table (\<lambda>x y. eval ((\<lambda>x. Det undefined)(''p'' := x, ''q'' := y)) p)
          (tv_pair_table tvs)"

fun
  string_of_nat :: "nat \<Rightarrow> string"
where
  "string_of_nat n = (if n < 10 then [char_of_nat (48 + n)] else
      string_of_nat (n div 10) @ [char_of_nat (48 + (n mod 10))])"

fun
  string_tv :: "tv \<Rightarrow> string"
where
  "string_tv (Det True) = ''*'' " |
  "string_tv (Det False) = ''o'' " |
  "string_tv (Indet n) = string_of_nat n"

definition
  appends :: "string list \<Rightarrow> string"
where
  "appends strs = foldr append strs []"

definition
  appends_nl :: "string list \<Rightarrow> string"
where
  "appends_nl strs = ''\<newline>  '' @
      foldr (\<lambda>x y. x @ ''\<newline>  '' @ y) (butlast strs) (last strs) @ ''\<newline>''"

definition
  string_table :: "tv list list \<Rightarrow> string list list"
where
  "string_table tvss = map (map string_tv) tvss"

definition
  string_table_string :: "string list list \<Rightarrow> string"
where
  "string_table_string strss = appends_nl (map appends strss)"

definition
  unary :: "fm \<Rightarrow> tv list \<Rightarrow> string"
where
  "unary p tvs = appends_nl (map string_tv (unary_truth_table p tvs))"

definition
  binary :: "fm \<Rightarrow> tv list \<Rightarrow> string"
where
  "binary p tvs = string_table_string (string_table (binary_truth_table p tvs))"

proposition
  "binary (Con (Pro ''p'') (Pro ''q''))
      [Det True, Det False, Indet 1, Indet 2] = ''
  *o12
  oooo
  1o1o
  2oo2
'' "
  by code_simp

proposition
  "binary (Dis (Pro ''p'') (Pro ''q''))
      [Det True, Det False, Indet 1, Indet 2] = ''
  ****
  *o12
  *11*
  *2*2
'' "
  by code_simp

proposition
  "unary (Neg' (Pro ''p''))
      [Det True, Det False, Indet 1, Indet 2] = ''
  o
  *
  1
  2
'' "
  by code_simp

proposition
  "binary (Eql (Pro ''p'') (Pro ''q''))
      [Det True, Det False, Indet 1, Indet 2] = ''
  *ooo
  o*oo
  oo*o
  ooo*
'' "
  by code_simp

proposition
  "binary (Imp (Pro ''p'') (Pro ''q''))
      [Det True, Det False, Indet 1, Indet 2] = ''
  *ooo
  ****
  *o*o
  *oo*
'' "
  by code_simp

proposition
  "unary (Box (Pro ''p''))
      [Det True, Det False, Indet 1, Indet 2] = ''
  *
  o
  o
  o
'' "
  by code_simp

proposition
  "binary (Eql' (Pro ''p'') (Pro ''q''))
      [Det True, Det False, Indet 1, Indet 2] = ''
  *o12
  o*12
  11*o
  22o*
'' "
  by code_simp

proposition
  "binary (Imp' (Pro ''p'') (Pro ''q''))
      [Det True, Det False, Indet 1, Indet 2] = ''
  *o12
  ****
  *1*1
  *22*
'' "
  by code_simp

proposition
  "unary (Neg (Pro ''p''))
      [Det True, Det False, Indet 1, Indet 2] = ''
  o
  *
  *
  *
'' "
  by code_simp

section \<open>Smaller Domains and Paraconsistency\<close>

definition
  domain :: "nat set \<Rightarrow> tv set"
where
  "domain U \<equiv> {Det True, Det False} \<union> Indet ` U"

theorem universal_domain: "domain {n. True} = {x. True}"
proof -
  have "\<forall>x. x = Det True \<or> x = Det False \<or> x \<in> range Indet"
    using range_eqI tv.collapse tv.inject
    by metis
  then show ?thesis
    unfolding domain_def
    by blast
qed

definition
  valid_in :: "nat set \<Rightarrow> fm \<Rightarrow> bool"
where
  "valid_in U p \<equiv> \<forall>i. range i \<subseteq> domain U \<longrightarrow> eval i p = Det True"

proposition "valid p \<longleftrightarrow> valid_in {n. True} p"
  unfolding valid_def valid_in_def
  using universal_domain
  by simp

theorem double_negation_in: "valid_in U (Neg' (Neg' p)) \<longleftrightarrow> valid_in U p"
  unfolding valid_in_def
  using eval_negation
  by auto

theorem conjunction_in: "valid_in U (Con p q) \<longleftrightarrow> valid_in U p \<and> valid_in U q"
  unfolding valid_in_def
  by auto

corollary "valid_in U (Con p q) \<Longrightarrow> valid_in U p"
  using conjunction_in
  by simp

corollary "valid_in U (Con p q) \<Longrightarrow> valid_in U q"
  using conjunction_in
  by simp

proposition "valid_in U p \<Longrightarrow> valid_in U (Imp p q) \<Longrightarrow> valid_in U q"
  unfolding valid_in_def
  using eval.simps tv.inject
  by (metis (full_types))

proposition "valid_in U p \<Longrightarrow> valid_in U (Imp' p q) \<Longrightarrow> valid_in U q"
  unfolding valid_in_def
  using eval.simps eval_equality
  by (metis (full_types))

lemma paraconsistency:
  "\<not> valid_in {1} (Imp' (Con (Pro ''P'') (Neg' (Pro ''P''))) (Pro ''Q''))"
proof -
  let ?i = "(\<lambda>s. Det False)(''P'' := Indet 1, ''Q'' := Det False)"
  have "range ?i \<subseteq> domain {1}"
    unfolding domain_def
    by auto
  moreover have "eval ?i (Imp' (Con (Pro ''P'') (Neg' (Pro ''P''))) (Pro ''Q'')) = Indet 1"
    by simp
  moreover have "Indet 1 \<noteq> Det True"
    by simp
  ultimately show ?thesis
    unfolding valid_in_def
    by metis
qed

theorem transfer: "\<not> valid_in U p \<Longrightarrow> \<not> valid p"
  unfolding valid_in_def valid_def
  by metis

proposition "\<not> valid (Imp' (Con (Pro ''P'') (Neg' (Pro ''P''))) (Pro ''Q''))"
  using paraconsistency transfer
  by simp

proposition "\<not> valid (Imp (Con (Pro ''P'') (Neg' (Pro ''P''))) (Pro ''Q''))"
  using paraconsistency transfer eval.simps tv.simps
  unfolding valid_in_def
  (* by smt OK *)
proof -
  assume *: "\<not> (\<forall>i. range i \<subseteq> domain U \<longrightarrow> eval i p = Det True) \<Longrightarrow> \<not> valid p" for U p
  assume "\<not> (\<forall>i. range i \<subseteq> domain {1} \<longrightarrow>
      eval i (Imp' (Con (Pro ''P'') (Neg' (Pro ''P''))) (Pro ''Q'')) = Det True)"
  then obtain i where
    **: "range i \<subseteq> domain {1} \<and>
        eval i (Imp' (Con (Pro ''P'') (Neg' (Pro ''P''))) (Pro ''Q'')) \<noteq> Det True"
    by blast
  then have "eval i (Con (Pro ''P'') (Neg' (Pro ''P''))) \<noteq>
      eval i (Con (Con (Pro ''P'') (Neg' (Pro ''P''))) (Pro ''Q''))"
    by force
  then show ?thesis
    using * **
    by force
qed

section \<open>Example: Contraposition\<close>

abbreviation (input)
  "contrapos P Q \<equiv> Eql' (Imp' P Q) (Imp' (Neg' Q) (Neg' P))"

proposition "valid_in {} (contrapos (Pro ''P'') (Pro ''Q''))"
  unfolding valid_in_def
proof (rule; rule)
  fix i :: "id \<Rightarrow> tv"
  assume "range i \<subseteq> domain {}"
  then have
      "i ''P'' \<in> {Det True, Det False}"
      "i ''Q'' \<in> {Det True, Det False}"
    unfolding domain_def
    by auto
  then show "eval i (contrapos (Pro ''P'') (Pro ''Q'')) = Det True"
    by (cases "i ''P''"; cases "i ''Q''") auto
qed

proposition "valid_in {1} (contrapos (Pro ''P'') (Pro ''Q''))"
  unfolding valid_in_def
proof (rule; rule)
  fix i :: "id \<Rightarrow> tv"
  assume "range i \<subseteq> domain {1}"
  then have
      "i ''P'' \<in> {Det True, Det False, Indet 1}"
      "i ''Q'' \<in> {Det True, Det False, Indet 1}"
    unfolding domain_def
    by auto
  then show "eval i (contrapos (Pro ''P'') (Pro ''Q'')) = Det True"
    by (cases "i ''P''"; cases "i ''Q''") auto
qed

proposition "\<not> valid_in {1,2} (contrapos (Pro ''P'') (Pro ''Q''))"
proof -
  let ?i = "(\<lambda>s. Det False)(''P'' := Indet 1, ''Q'' := Indet 2)"
  have "range ?i \<subseteq> domain {1, 2}"
    unfolding domain_def
    by auto
  moreover have "eval ?i (contrapos (Pro ''P'') (Pro ''Q'')) = Det False"
    by simp
  moreover have "Det False \<noteq> Det True"
    by simp
  ultimately show ?thesis
    unfolding valid_in_def
    by metis
qed

section \<open>Four Truth Values Are Not Enough\<close>

abbreviation (input)
  "ternary P Q R \<equiv>
      Imp' (Neg' (Imp' Q P))
          (Imp' (Neg' (Dis (Neg' R) (Imp' R Q))) (Imp' P Q))"

proposition "valid_in {} (ternary (Pro ''P'') (Pro ''Q'') (Pro ''R''))"
  unfolding valid_in_def
proof (rule; rule)
  fix i :: "id \<Rightarrow> tv"
  assume "range i \<subseteq> domain {}"
  then have
      "i ''P'' \<in> {Det True, Det False}"
      "i ''Q'' \<in> {Det True, Det False}"
      "i ''R'' \<in> {Det True, Det False}"
    unfolding domain_def
    by auto
  then show "eval i (ternary (Pro ''P'') (Pro ''Q'') (Pro ''R'')) = Det True"
    by (cases "i ''P''"; cases "i ''Q''"; cases "i ''R''") auto
qed

proposition "valid_in {1} (ternary (Pro ''P'') (Pro ''Q'') (Pro ''R''))"
  unfolding valid_in_def
proof (rule; rule)
  fix i :: "id \<Rightarrow> tv"
  assume "range i \<subseteq> domain {1}"
  then have
      "i ''P'' \<in> {Det True, Det False, Indet 1}"
      "i ''Q'' \<in> {Det True, Det False, Indet 1}"
      "i ''R'' \<in> {Det True, Det False, Indet 1}"
    unfolding domain_def
    by auto
  then show "eval i (ternary (Pro ''P'') (Pro ''Q'') (Pro ''R'')) = Det True"
    by (cases "i ''P''"; cases "i ''Q''"; cases "i ''R''") auto
qed

proposition "valid_in {1,2} (ternary (Pro ''P'') (Pro ''Q'') (Pro ''R''))"
  unfolding valid_in_def
proof (rule; rule)
  fix i :: "id \<Rightarrow> tv"
  assume "range i \<subseteq> domain {1,2}"
  then have
      "i ''P'' \<in> {Det True, Det False, Indet 1, Indet 2}"
      "i ''Q'' \<in> {Det True, Det False, Indet 1, Indet 2}"
      "i ''R'' \<in> {Det True, Det False, Indet 1, Indet 2}"
    unfolding domain_def
    by auto
  then show "eval i (ternary (Pro ''P'') (Pro ''Q'') (Pro ''R'')) = Det True"
    by (cases "i ''P''"; cases "i ''Q''"; cases "i ''R''") auto
qed

proposition "\<not> valid_in {1,2,3} (ternary (Pro ''P'') (Pro ''Q'') (Pro ''R''))"
proof -
  let ?i = "(\<lambda>s. Det False)(''P'' := Indet 2, ''Q'' := Indet 1, ''R'' := Indet 3)"
  have "range ?i \<subseteq> domain {1, 2, 3}"
    unfolding domain_def
    by auto
  moreover have "eval ?i (ternary (Pro ''P'') (Pro ''Q'') (Pro ''R'')) = Indet 1"
    by simp
  moreover have "Indet 1 \<noteq> Det True"
    by simp
  ultimately show ?thesis
    unfolding valid_in_def
    by metis
qed

section \<open>Meta-Theorems\<close>

theorem valid_valid_in:
  assumes "valid p"
  shows "valid_in U p"
  using assms transfer
  by blast

fun
  props :: "fm \<Rightarrow> id set"
where
  "props Truth = {}" |
  "props (Pro s) = {s}" |
  "props (Neg' p) = props p" |
  "props (Con p q) = props p \<union> props q" |
  "props (Eql p q) = props p \<union> props q" |
  "props (Eql' p q) = props p \<union> props q"

lemma relevant_props:
  assumes "\<forall>s \<in> props p. i1 s = i2 s"
  shows "eval i1 p = eval i2 p"
  using assms
  by (induct p) (simp_all, metis)

fun
  change_tv :: "(nat \<Rightarrow> nat) \<Rightarrow> tv \<Rightarrow> tv"
where
  "change_tv f (Det b) = Det b" |
  "change_tv f (Indet n) = Indet (f n)"

lemma change_tv_injection:
  assumes "inj f"
  shows "inj (change_tv f)"
proof -
  {
    fix tv1 tv2
    have "inj f \<Longrightarrow> change_tv f tv1 = change_tv f tv2 \<Longrightarrow> tv1 = tv2"
      by (cases tv1; cases tv2) (simp_all add: inj_eq)
  }
  then show ?thesis
    using assms
    by (simp add: injI)
qed

definition
  change_int :: "(nat \<Rightarrow> nat) \<Rightarrow> (id \<Rightarrow> tv) \<Rightarrow> (id \<Rightarrow> tv)"
where
  "change_int f i \<equiv> \<lambda>s. change_tv f (i s)"

lemma eval_change_int_change_tv:
  assumes "inj f"
  shows "eval (change_int f i) p = change_tv f (eval i p)"
proof (induct p)
  fix p
  assume a: "eval (change_int f i) p = change_tv f (eval i p)"
  have "eval_neg (eval (change_int f i) p) = eval_neg (change_tv f (eval i p))"
    using assms a
    by auto
  then have "eval_neg (eval (change_int f i) p) = change_tv f (eval_neg (eval i p))"
    by (cases "eval i p") (auto simp add: case_bool_if)
  then show "eval (change_int f i) (Neg' p) = change_tv f (eval i (Neg' p))"
    by auto
next
  fix p1 p2
  assume ih1: "eval (change_int f i) p1 = change_tv f (eval i p1)"
  assume ih2: "eval (change_int f i) p2 = change_tv f (eval i p2)"
  show "eval (change_int f i) (Con p1 p2) = change_tv f (eval i (Con p1 p2))"
  proof (cases "eval i p1 = eval i p2")
    assume a: "eval i p1 = eval i p2"
    then have yes: "eval i (Con p1 p2) = eval i p1"
      by auto
    from a have "change_tv f (eval i p1) = change_tv f (eval i p2)"
      by auto
    then have "eval (change_int f i) p1 = eval (change_int f i) p2"
      using ih1 ih2
      by auto
    then have "eval (change_int f i) (Con p1 p2) = eval (change_int f i) p1"
      by auto
    then show "eval (change_int f i) (Con p1 p2) = change_tv f (eval i (Con p1 p2))"
      using yes ih1
      by auto
  next
    assume a': "eval i p1 \<noteq> eval i p2"
    from a' have b': "eval (change_int f i) p1 \<noteq> eval (change_int f i) p2"
      using \<open>inj f\<close> ih1 ih2 change_tv_injection the_inv_f_f
      by metis
    show "eval (change_int f i) (Con p1 p2) = change_tv f (eval i (Con p1 p2))"
    proof (cases "eval i p1 = Det True")
      assume a: "eval i p1 = Det True"
      from a a' have "eval i (Con p1 p2) = eval i p2"
        by auto
      then have c: "change_tv f (eval i (Con p1 p2)) = change_tv f (eval i p2)"
        by auto
      from a have b: "eval (change_int f i) p1 = Det True"
        using ih1
        by auto
      from b b' have "eval (change_int f i) (Con p1 p2) = eval (change_int f i) p2"
        by auto
      then show "eval (change_int f i) (Con p1 p2) = change_tv f (eval i (Con p1 p2))"
        using c ih2
        by auto
    next
      assume a'': "eval i p1 \<noteq> Det True"
      from a'' have b'': "eval (change_int f i) p1 \<noteq> Det True"
        using \<open>inj f\<close> ih1 ih2 change_tv_injection the_inv_f_f change_tv.simps
        by metis
      show "eval (change_int f i) (Con p1 p2) = change_tv f (eval i (Con p1 p2))"
      proof (cases "eval i p2 = Det True")
        assume a: "eval i p2 = Det True"
        from a a' a'' have "eval i (Con p1 p2) = eval i p1"
          by auto
        then have c: "change_tv f (eval i (Con p1 p2)) = change_tv f (eval i p1)"
          by auto
        from a have b: "eval (change_int f i) p2 = Det True"
          using ih2
          by auto
        from b b' b'' have "eval (change_int f i) (Con p1 p2) = eval (change_int f i) p1"
          by auto
        then show "eval (change_int f i) (Con p1 p2) = change_tv f (eval i (Con p1 p2))"
          using c ih1
          by auto
      next
        assume a''': "eval i p2 \<noteq> Det True"
        from a' a'' a''' have "eval i (Con p1 p2) = Det False"
          by auto
        then have c: "change_tv f (eval i (Con p1 p2)) = Det False"
          by auto
        from a''' have b''': "eval (change_int f i) p2 \<noteq> Det True"
          using \<open>inj f\<close> ih1 ih2 change_tv_injection the_inv_f_f change_tv.simps
          by metis
        from b' b'' b''' have "eval (change_int f i) (Con p1 p2) = Det False"
          by auto
        then show "eval (change_int f i) (Con p1 p2) = change_tv f (eval i (Con p1 p2))"
          using c
          by auto
      qed
    qed
  qed
next
  fix p1 p2
  assume ih1: "eval (change_int f i) p1 = change_tv f (eval i p1)"
  assume ih2: "eval (change_int f i) p2 = change_tv f (eval i p2)"
  have "Det (eval (change_int f i) p1 = eval (change_int f i) p2) =
      Det (change_tv f (eval i p1) = change_tv f (eval i p2))"
    using ih1 ih2
    by auto
  also have "... = Det ((eval i p1) = (eval i p2))"
    using assms change_tv_injection
    by (simp add: inj_eq)
  also have "... = change_tv f (Det (eval i p1 = eval i p2))"
    by auto
  finally
  show "eval (change_int f i) (Eql p1 p2) = change_tv f (eval i (Eql p1 p2))"
    using eval_equality
    by auto
next
  fix p1 p2
  assume ih1: "eval (change_int f i) p1 = change_tv f (eval i p1)"
  assume ih2: "eval (change_int f i) p2 = change_tv f (eval i p2)"
  show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
  proof (cases "eval i p1 = eval i p2")
    assume a: "eval i p1 = eval i p2"
    then have yes: "eval i (Eql' p1 p2) = Det True"
      by auto
    from a have "change_tv f (eval i p1) = change_tv f (eval i p2)"
      by auto
    then have "eval (change_int f i) p1 = eval (change_int f i) p2"
      using ih1 ih2
      by auto
    then have "eval (change_int f i) (Eql' p1 p2) = Det True"
      by auto
    then show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
      using yes ih1
      by auto
  next
    assume a': "eval i p1 \<noteq> eval i p2"
    show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
    proof (cases "eval i p1 = Det True")
      assume a: "eval i p1 = Det True"
      from a a' have yes: "eval i (Eql' p1 p2) = eval i p2"
        by auto
      from a have "change_tv f (eval i p1) = Det True"
        by auto
      then have b: "eval (change_int f i) p1 = Det True"
        using ih1
        by auto
      from a' have b': "eval (change_int f i) p1 \<noteq> eval (change_int f i) p2"
        using \<open>inj f\<close> ih1 ih2 change_tv_injection the_inv_f_f change_tv.simps
        by metis
      from b b' have "eval (change_int f i) (Eql' p1 p2) = eval (change_int f i) p2"
        by auto
      then show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
        using ih2 yes
        by auto
    next
      assume a'': "eval i p1 \<noteq> Det True"
      show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
      proof (cases "eval i p2 = Det True")
        assume a: "eval i p2 = Det True"
        from a a' a'' have yes: "eval i (Eql' p1 p2) = eval i p1"
          using eval_equality[of i p1 p2]
          by auto
        from a have "change_tv f (eval i p2) = Det True"
          by auto
        then have b: "eval (change_int f i) p2 = Det True"
          using ih2
          by auto
        from a' have b': "eval (change_int f i) p1 \<noteq> eval (change_int f i) p2"
          using \<open>inj f\<close> ih1 ih2 change_tv_injection the_inv_f_f change_tv.simps
          by metis
        from a'' have b'': "eval (change_int f i) p1 \<noteq> Det True"
          using b b'
          by auto
        from b b' b'' have "eval (change_int f i) (Eql' p1 p2) = eval (change_int f i) p1"
          using eval_equality[of "change_int f i" p1 p2]
          by auto
        then show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
          using ih1 yes
          by auto
      next
        assume a''': "eval i p2 \<noteq> Det True"
        show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
        proof (cases "eval i p1 = Det False")
          assume a: "eval i p1 = Det False"
          from a a' a'' a''' have yes: "eval i (Eql' p1 p2) = eval i (Neg' p2)"
            using eval_equality[of i p1 p2]
            by auto
          from a have "change_tv f (eval i p1) = Det False"
            by auto
          then have b: "eval (change_int f i) p1 = Det False"
            using ih1
             by auto
          from a' have b': "eval (change_int f i) p1 \<noteq> eval (change_int f i) p2"
            using \<open>inj f\<close> ih1 ih2 change_tv_injection the_inv_f_f change_tv.simps
            by metis
          from a'' have b'': "eval (change_int f i) p1 \<noteq> Det True"
            using b b'
            by auto
          from a''' have b''': "eval (change_int f i) p2 \<noteq> Det True"
            using b b' b''
            by (metis assms change_tv.simps(1) change_tv_injection inj_eq ih2)
          from b b' b'' b'''
          have "eval (change_int f i) (Eql' p1 p2) = eval (change_int f i) (Neg' p2)"
            using eval_equality[of "change_int f i" p1 p2]
            by auto
          then show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
            using ih2 yes a a' a''' b b' b''' eval_negation
            by metis
        next
          assume a'''': "eval i p1 \<noteq> Det False"
          show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
          proof (cases "eval i p2 = Det False")
            assume a: "eval i p2 = Det False"
            from a a' a'' a''' a'''' have yes: "eval i (Eql' p1 p2) = eval i (Neg' p1)"
              using eval_equality[of i p1 p2]
              by auto
            from a have "change_tv f (eval i p2) = Det False"
              by auto
            then have b: "eval (change_int f i) p2 = Det False"
              using ih2
              by auto
            from a' have b': "eval (change_int f i) p1 \<noteq> eval (change_int f i) p2"
              using \<open>inj f\<close> ih1 ih2 change_tv_injection the_inv_f_f change_tv.simps
              by metis
            from a'' have b'': "eval (change_int f i) p1 \<noteq> Det True"
              using change_tv.elims ih1 tv.simps(4)
              by auto
            from a''' have b''': "eval (change_int f i) p2 \<noteq> Det True"
              using b b' b''
              by (metis assms change_tv.simps(1) change_tv_injection inj_eq ih2)
            from a'''' have b'''': "eval (change_int f i) p1 \<noteq> Det False"
              using b b'
              by auto
            from b b' b'' b''' b''''
            have "eval (change_int f i) (Eql' p1 p2) = eval (change_int f i) (Neg' p1)"
              using eval_equality[of "change_int f i" p1 p2]
              by auto
            then show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
              using ih1 yes a a' a''' a'''' b b' b''' b'''' eval_negation a'' b''
              by metis
          next
            assume a''''': "eval i p2 \<noteq> Det False"
            from a' a'' a''' a'''' a''''' have yes: "eval i (Eql' p1 p2) = Det False"
              using eval_equality[of i p1 p2]
              by auto
            from a''''' have "change_tv f (eval i p2) \<noteq> Det False"
              using change_tv_injection inj_eq \<open>inj f\<close> change_tv.simps
              by metis
            then have b: "eval (change_int f i) p2 \<noteq> Det False"
              using ih2
              by auto
            from a' have b': "eval (change_int f i) p1 \<noteq> eval (change_int f i) p2"
              using \<open>inj f\<close> ih1 ih2 change_tv_injection the_inv_f_f change_tv.simps
              by metis
            from a'' have b'': "eval (change_int f i) p1 \<noteq> Det True"
              using change_tv.elims ih1 tv.simps(4)
              by auto
            from a''' have b''': "eval (change_int f i) p2 \<noteq> Det True"
              using b b' b''
              by (metis assms change_tv.simps(1) change_tv_injection the_inv_f_f ih2)
            from a'''' have b'''': "eval (change_int f i) p1 \<noteq> Det False"
              by (metis a'' change_tv.simps(2) ih1 string_tv.cases tv.distinct(1))
            from b b' b'' b''' b'''' have "eval (change_int f i) (Eql' p1 p2) = Det False"
              using eval_equality[of "change_int f i" p1 p2]
              by auto
            then show "eval (change_int f i) (Eql' p1 p2) = change_tv f (eval i (Eql' p1 p2))"
              using ih1 yes a' a''' a'''' b b' b''' b'''' eval_negation a'' b''
              by auto
          qed
        qed
      qed
    qed
  qed
qed (simp_all add: change_int_def)

theorem valid_in_valid:
  assumes "card U \<ge> card (props p)"
  assumes "valid_in U p"
  shows "valid p"
proof -
  have "finite U \<Longrightarrow> card (props p) \<le> card U \<Longrightarrow> valid_in U p \<Longrightarrow> valid p" for U p
  proof -
    assume assms: "finite U" "card (props p) \<le> card U" "valid_in U p"
    show "valid p"
      unfolding valid_def
    proof
      fix i
      obtain f where f_p: "(change_int f i) ` (props p) \<subseteq> (domain U) \<and> inj f"
      proof -
        have "finite U \<Longrightarrow> card (props p) \<le> card U \<Longrightarrow>
            \<exists>f. change_int f i ` props p \<subseteq> domain U \<and> inj f" for U p
        proof -
          assume assms: "finite U" "card (props p) \<le> card U"
          show ?thesis
          proof -
            let ?X = "(get_indet ` ((i ` props p) \<inter> {tv. is_indet tv}))"
            have d: "finite (props p)"
              by (induct p) auto
            then have f: "finite ?X"
              by auto
            have cx: "card ?X \<le> card U"
              using assms
              by (metis Int_lower1 d card_image_le card_mono finite_Int finite_imageI le_trans)
            obtain f where f_p: "(\<forall>n \<in> ?X. f n \<in> U) \<and> (inj f)"
            proof -
              have "finite X \<Longrightarrow> finite Y \<Longrightarrow> card X \<le> card Y \<Longrightarrow> \<exists>f. (\<forall>n\<in>X. f n \<in> Y) \<and> inj f"
                  for X Y :: "nat set"
              proof -
                assume assms: "finite X" "finite Y" "card X \<le> card Y"
                show ?thesis
                proof -
                  from assms obtain Z where "Z \<subseteq> Y \<and> card Z = card X"
                    by (metis card_image card_le_inj)
                  then obtain f where "bij_betw f X Z"
                    by (metis assms(1) assms(2) finite_same_card_bij infinite_super)
                  then have f_p: "(\<forall>n \<in> X. f n \<in> Y) \<and> inj_on f X"
                    using \<open>Z \<subseteq> Y \<and> card Z = card X\<close> bij_betwE bij_betw_imp_inj_on
                    by blast
                  obtain f' where f': "f' = (\<lambda>n. if n \<in> X then f n else n + Suc (Max Y + n))"
                    by simp
                  have "inj f'"
                    unfolding f' inj_on_def
                    using assms(2) f_p le_add2 trans_le_add2 not_less_eq_eq
                    by (simp, metis Max_ge add.commute inj_on_eq_iff)
                  moreover have "(\<forall>n \<in> X. f' n \<in> Y)"
                    unfolding f'
                    using f_p
                    by auto
                  ultimately show ?thesis
                    by metis
                qed
              qed
              then show "(\<And>f. (\<forall>n \<in> get_indet ` (i ` props p \<inter> {tv. is_indet tv}). f n \<in> U)
                  \<and> inj f \<Longrightarrow> thesis) \<Longrightarrow> thesis"
                using assms cx f
                unfolding inj_on_def
                by metis
            qed
            have "(change_int f i) ` (props p) \<subseteq> (domain U)"
            proof
              fix x
              assume "x \<in> change_int f i ` props p"
              then obtain s where s_p: "s \<in> props p \<and> change_int f i s = x"
                by auto
              then have "change_int f i s \<in> {Det True, Det False} \<union> Indet ` U"
              proof (cases "change_int f i s \<in> {Det True, Det False}")
                case True
                then show ?thesis
                  by auto
              next
                case False
                then obtain n' where "change_int f i s = Indet n'"
                  by (cases "change_int f i s") auto
                then have p: "change_tv f (i s) = Indet n'"
                  by (simp add: change_int_def)
                moreover
                {
                  obtain n'' where "f n'' = n'"
                    using calculation change_tv.elims
                    by blast
                  moreover have "s \<in> props p \<and> i s = (Indet n'')"
                    using p calculation change_tv.simps change_tv_injection the_inv_f_f f_p s_p
                    by metis
                  then have "(Indet n'') \<in> i ` props p"
                    using image_iff
                    by metis
                  then have "(Indet n'') \<in> i ` props p \<and> is_indet (Indet n'') \<and>
                      get_indet (Indet n'') = n''"
                    by auto
                  then have "n'' \<in> ?X"
                    using Int_Collect image_iff
                    by metis
                  ultimately have "n' \<in> U"
                    using f_p
                    by auto
                }
                ultimately have "change_tv f (i s) \<in> Indet ` U"
                  by auto
                then have "change_int f i s \<in> Indet ` U"
                  unfolding change_int_def
                  by auto
                then show ?thesis
                  by auto
              qed
              then show "x \<in> domain U"
                unfolding domain_def
                using s_p
                by simp
            qed
            then have "(change_int f i) ` (props p) \<subseteq> (domain U) \<and> (inj f)"
              unfolding domain_def
              using f_p
              by simp
            then show ?thesis
              using f_p
              by metis
          qed
        qed
        then show "(\<And>f. change_int f i ` props p \<subseteq> domain U \<and> inj f \<Longrightarrow> thesis) \<Longrightarrow> thesis"
          using assms
          by metis
      qed
      obtain i2 where i2: "i2 = (\<lambda>s. if s \<in> props p then (change_int f i) s else Det True)"
        by simp
      then have i2_p: "\<forall>s \<in> props p. i2 s = (change_int f i) s"
            "\<forall>s \<in> - props p. i2 s = Det True"
        by auto
      then have "range i2 \<subseteq> (domain U)"
        using i2 f_p
        unfolding domain_def
        by auto
      then have "eval i2 p = Det True"
        using assms
        unfolding valid_in_def
        by auto
      then have "eval (change_int f i) p = Det True"
        using relevant_props[of p i2 "change_int f i"] i2_p
        by auto
      then have "change_tv f (eval i p) = Det True"
        using eval_change_int_change_tv f_p
        by auto
      then show "eval i p = Det True"
        by (cases "eval i p") auto
    qed
  qed
  then show ?thesis
    using assms subsetI sup_bot.comm_neutral image_is_empty subsetCE UnCI valid_in_def
        Un_insert_left card.empty card.infinite finite.intros(1)
    unfolding domain_def
    by metis
qed

proposition "valid p \<longleftrightarrow> valid_in {1..card (props p)} p"
  using valid_in_valid transfer
  by force

end
