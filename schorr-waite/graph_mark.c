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

void graph_mark_recursive(struct node * p) {
  if (p && !p->mark) {
    p->mark = 3;
    graph_mark_recursive(p->left);
    graph_mark_recursive(p->right);
  }
}
