function h$_foundation_memcmp(s1, o1, off1, s2, o2, off2, n) {
    h$memcmp(s1, o1 + off2, s2, o2 + off2, n);
}
