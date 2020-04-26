#include "stdlib.h"
#include "stdio.h"

#define HUNDRED_M 100000000
#define TEN_M      10000000
#define TEN_K         10000
#define TEN              10

#define GEN(i) (((i) % 10) - 2 * ((i) % 7))

#if BENCHMARK_sum
int main(void) {
  int sum = 0;
  for (int i = 0; i < HUNDRED_M; ++i) {
    sum += GEN(i);
  }
  printf("%d\n", sum);
  return 0;
}
#endif

#if BENCHMARK_sumOfSquares
int main(void) {
  int sum = 0;
  for (int i = 0; i < HUNDRED_M; ++i) {
    sum += GEN(i) * GEN(i);
  }
  printf("%d\n", sum);
  return 0;
}
#endif

#if BENCHMARK_sumOfSquaresEven
int main(void) {
  int sum = 0;
  for (int i = 0; i < HUNDRED_M; ++i) {
    int x = GEN(i);
    if (x % 2 == 0) {
      sum += x * x;
    }
  }
  printf("%d\n", sum);
  return 0;
}
#endif

#if BENCHMARK_cart
int main(void) {
  int sum = 0;
  for (int i = 0; i < TEN_M; ++i) {
    for (int j = 0; j < TEN; ++j) {
      sum += GEN(i) * GEN(j);
    }
  }
  printf("%d\n", sum);
  return 0;
}
#endif

#if BENCHMARK_maps
int main(void) {
  for (int i = 0; i < HUNDRED_M; ++i) {
    printf("%d\n", GEN(i) * 2 * 3);
  }
  return 0;
}
#endif

#if BENCHMARK_filters
int main(void) {
  for (int i = 0; i < HUNDRED_M; ++i) {
    int y = GEN(i);
    if (y % 5 != 0 && y % 8 != 0) {
      printf("%d\n", y);
    }
  }
  return 0;
}
#endif

#if BENCHMARK_dotProduct
int main(void) {
  int sum = 0;
  for (int i = 0; i < TEN_M; ++i) {
    sum += GEN(i) * GEN(i);
  }
  printf("%d\n", sum);
  return 0;
}
#endif

#if BENCHMARK_flatmap_after_zipWith
int main(void) {
  for (int i = 0; i < TEN_K; ++i) {
    for (int j = 0; j < TEN_K; ++j) {
      printf("%d\n", (GEN(i) + GEN(i)) * GEN(j));
    }
  }
  return 0;
}
#endif

#if BENCHMARK_zipWith_after_flatmap
int main(void) {
  for (int i = 0; i < TEN_K; ++i) {
    for (int j = 0; j < TEN_K; ++j) {
      printf("%d\n", GEN(i * TEN_K + j) + (GEN(j) + GEN(j)));
    }
  }
  return 0;
}
#endif

#if BENCHMARK_flatmap_take
int main(void) {
  // Emit 20,000,000 items
  for (int i = 0; i < 2000; ++i) {
    for (int j = 0; j < TEN_K; ++j) {
      printf("%d\n", GEN(i) + GEN(j));
    }
  }
  return 0;
}
#endif
