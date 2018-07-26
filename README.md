# Einstein's Puzzle
A practice of using coq to prove the result of Einstein's puzzle. The puzzle itself can be found in http://www.chessandpoker.com/einsteins-problem-solution.html.

## Prolog file
The prolog file is a search algorithm to ensure the existance of satisfiable interpretation, it's based on the code from https://gist.github.com/jgilchrist/1b85b04f4395057972dd. However the original code there cannot force bijectivity between houses, colors etc. For example, if remove the green requirement in the fourth member condition, the returned solution will have different houses with same colors. So I add two predicates to correct this.

## Coq files
Coq (https://coq.inria.fr/) is a proof assistant based on calculus of inductive construction, a implementation of intuitionistic type theory. Two coq files contain the whole description of the einstein's puzzle as well as the full formal proof.

The version 0 is more like a straightforwad proof with little modularity and a few high-level theorems. The problem definition is described in http://fixedpoint.jp/2016/08/02/five-houses.html. The main problem in this proof is that it's pretty cumbersome to prove some claims backwards from the axioms using bijectivity. 

The version 1 defined two bijective function explicitly, and using them to describe the axioms. Furthermore, some high level theorems are extracted first. With the help of these tools, the proof become more fluent.


