int test_fold(int (*op)(int, int), int n) {
    int res = 0;
    for(int i = 0; i <= n; i++) {
        res = op(i,res);
    }
    return res;
}