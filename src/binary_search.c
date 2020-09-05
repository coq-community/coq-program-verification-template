int binary_search(int a[], int len, int key) {
  int low = 0;
  int high = len - 1;

  while (low <= high) {
    int mid = ((unsigned int)low + (unsigned int)high) >> 1;
    int mid_val = a[mid];
    if (mid_val < key)
      low = mid + 1;
    else if (mid_val > key)
      high = mid - 1;
    else
      return mid;
  }
  return -low - 1;
}

int four[4] = {1, 2, 3, 4};

int main() {
  int s = binary_search(four, 4, 3);
  return s;
}
