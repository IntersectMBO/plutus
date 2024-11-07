-- chooseList should accept arbitrary terms in the branches
(program 0.0.0 [[[(force (force (builtin chooseList))) (con (list integer) [ ])] (lam x x)] (lam y (lam z z))])