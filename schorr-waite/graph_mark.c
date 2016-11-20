// The Schorr-Waite graph-marking procedure.
//
// This version is based on a description by David Gries, modified to allow null pointers
// anywhere in the graph (including the root).
//
// http://www.cs.cornell.edu/courses/cs312/2007fa/lectures/lec21-schorr-waite.pdf
// (retrieved 4 September 2016).

struct node {
  struct node * left;
  struct node * right;
  unsigned mark;
};

void graph_mark(struct node * p) {
  struct node * q = 0;
  while (p) {
    p->mark++;
    if (p->mark == 3 || p->left && p->left->mark == 0) {
      // rotate [ q, p, p->left, p->right ]
      struct node * t = p;
      p = t->left;
      t->left = t->right;
      t->right = q;
      q = t;
    }
    else {
      // rotate [ q, p->left, p->right ]
      struct node * t = p->left;
      p->left = p->right;
      p->right = q;
      q = t;
    }
  }
}

// A recursive graph-marking procedure,
// which can be regarded as an executable specification.

void graph_mark_recursive(struct node * p) {
  if (p && !p->mark) {
    p->mark = 3;
    graph_mark_recursive(p->left);
    graph_mark_recursive(p->right);
  }
}
