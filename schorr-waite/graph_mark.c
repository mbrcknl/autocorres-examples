struct node {
  struct node * left;
  struct node * right;
  unsigned mark;
};

void graph_mark(struct node * p) {
  struct node * q = 0;
  while (p) {
    p->mark++;
    if (p->mark == 3 || p->left != 0 && p->left->mark == 0) {
      struct node * t = p;
      p = t->left;
      t->left = t->right;
      t->right = q;
      q = t;
    }
    else {
      struct node * t = p->left;
      p->left = p->right;
      p->right = q;
      q = t;
    }
  }
}
