#include "stdlib.h"

#define HUNDRED_M 100000000
#define TEN_M      10000000
#define TEN_K         10000
#define TEN              10

#define CREATE(a, n) \
  int* a = malloc(n * sizeof(int));\
  for (int i = 0; i < n; ++i) { \
    a[i] = i % 10; \
  }

#if BENCHMARK_sum
int main(void) {
  CREATE(arr, HUNDRED_M);
  volatile int sum = 0;
  for (int i = 0; i < HUNDRED_M; ++i) {
    sum += arr[i];
  }
  return 0;
}
#endif

#if BENCHMARK_sumOfSquares
int main(void) {
  CREATE(arr, HUNDRED_M);
  volatile int sum = 0;
  for (int i = 0; i < HUNDRED_M; ++i) {
    sum += arr[i] * arr[i];
  }
  return 0;
}
#endif

#if BENCHMARK_sumOfSquaresEven
int main(void) {
  CREATE(arr, HUNDRED_M);
  volatile int sum = 0;
  for (int i = 0; i < HUNDRED_M; ++i) {
    int x = arr[i];
    if (x % 2 == 0) {
      sum += x * x;
    }
  }
  return 0;
}
#endif

#if BENCHMARK_cart
int main(void) {
  CREATE(x, TEN_M);
  CREATE(y, TEN);
  volatile int sum = 0;
  for (int i = 0; i < TEN_M; ++i) {
    for (int j = 0; j < TEN; ++j) {
      sum += x[i] * y[j];
    }
  }
  return 0;
}
#endif

#if BENCHMARK_maps
int main(void) {
  CREATE(arr, HUNDRED_M);
  volatile int x = 0;
  for (int i = 0; i < HUNDRED_M; ++i) {
    x = arr[i] * 2 * 3;
  }
  return 0;
}
#endif

#if BENCHMARK_filters
int main(void) {
  CREATE(arr, HUNDRED_M);
  volatile int x = 0;
  for (int i = 0; i < HUNDRED_M; ++i) {
    int y = arr[i];
    if (y % 5 != 0 && y % 8 != 0) {
      x = y;
    }
  }
  return 0;
}
#endif

#if BENCHMARK_dotProduct
int main(void) {
  CREATE(x, TEN_M);
  CREATE(y, TEN_M);
  volatile int n = 0;
  for (int i = 0; i < TEN_M; ++i) {
    n = x[i] * y[i];
  }
  return 0;
}
#endif

#if BENCHMARK_flatmap_after_zipWith
int main(void) {
  CREATE(x, TEN_K);
  CREATE(y, TEN_K);
  CREATE(z, TEN_K);
  volatile int n = 0;
  for (int i = 0; i < TEN_K; ++i) {
    for (int j = 0; j < TEN_K; ++j) {
      n = (x[i] + y[i]) * z[j];
    }
  }
  return 0;
}
#endif

#if BENCHMARK_zipWith_after_flatmap
int main(void) {
  CREATE(x, HUNDRED_M);
  CREATE(y, TEN_K);
  CREATE(z, TEN_K);
  volatile int n = 0;
  for (int i = 0; i < TEN_K; ++i) {
    for (int j = 0; j < TEN_K; ++j) {
      n = x[i * TEN_K + j] + (y[j] + z[j]);
    }
  }
  return 0;
}
#endif

#if BENCHMARK_flatmap_take
int main(void) {
  CREATE(x, TEN_K);
  CREATE(y, TEN_K);
  volatile int n = 0;
  int d = 0;
  for (int i = 0; i < TEN_K && d < 20000000; ++i) {
    for (int j = 0; j < TEN_K && d < 20000000; ++j) {
      n = x[i] + y[j];
      ++d;
    }
  }
  return 0;
}
#endif
