unsigned int bvalue(unsigned int method, unsigned long node_id) {
    switch (method) {
        default: return (unsigned) (2 * node_id + method) % 10;
        case 0: return 4;
        case 1: return 7;
    }
}
