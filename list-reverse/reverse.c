struct node {
  struct node * next;
  int value;
};

struct node * reverse(struct node * list) {
  struct node * result = 0;
  while (list) {
    struct node * tmp = list->next;
    list->next = result;
    result = list;
    list = tmp;
  }
  return result;
}
