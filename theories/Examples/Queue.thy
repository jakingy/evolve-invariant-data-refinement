theory Queue
  imports Main "HOL-Library.Sublist"
begin

datatype 'a queue = Queue "'a list"

definition empty :: "'a queue" where
  "empty = Queue []"

fun enqueue :: "'a queue \<Rightarrow> 'a \<Rightarrow> 'a queue" where
  "enqueue (Queue xs) x = Queue (xs @ [x])"

fun dequeue :: "'a queue \<Rightarrow> ('a \<times> 'a queue) option" where
  "dequeue (Queue []) = None"
| "dequeue (Queue (x # xs)) = Some (x, Queue xs)"

fun q_concat_front :: "'a \<Rightarrow> 'a queue \<Rightarrow> 'a queue" where
  "q_concat_front x (Queue xs) = Queue (x # xs)"

fun is_empty :: "'a queue \<Rightarrow> bool" where
  "is_empty (Queue xs) = (xs = [])"

fun q_size :: "'a queue \<Rightarrow> nat" where
  "q_size (Queue xs) = length xs"

fun q_suffix :: "'a queue \<Rightarrow> 'a queue \<Rightarrow> bool" where
  "q_suffix (Queue xs) (Queue ys) = suffix xs ys"

fun q_prefix :: "'a queue \<Rightarrow> 'a queue \<Rightarrow> bool" where
  "q_prefix (Queue xs) (Queue ys) = prefix xs ys"

lemma q_prefix_eq: "q_prefix x x"
  using q_prefix.elims(3) by blast

lemma q_suffix_eq: "q_suffix x x"
  by (cases x) simp

end
