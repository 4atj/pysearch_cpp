#include <cstdio>
#include <numeric>
#include <unordered_map>
#include <unordered_set>
#include <valarray>
#include <vector>
#include <cstdint>
#include <bitset>
#include <iostream>
#include <omp.h>

using value_t = int32_t;

using Vec = std::valarray<value_t>;
const value_t int_min = std::numeric_limits<value_t>::min();
struct Input { const char *name; Vec vec; };

// ---- start of parameters ---

static const Input inputs[] = {
  {"a", {0,1,2,3,4,5,6,7,8,9}},
};

static const Vec goals[] = {
  {0,0,1,0,1,2,0,1,2,3},
};

const int num_vars = sizeof(inputs) / sizeof(inputs[0]);

const int max_length = 12;
const int max_cache_length = max_length - 4;

static const value_t literals[] = {};
#define use_literals_range true
#if use_literals_range == true
  const value_t min_literal = 1;
  const value_t max_literal = 10;
#endif

const bool Use_Or = false;
const bool Use_Lt = false;
const bool Use_Leq = false;
const bool Use_BitOr = true;
const bool Use_BitXor = true;
const bool Use_BitAnd = true;
const bool Use_BitShl = true;
const bool Use_BitShr = true;
const bool Use_BitNeg = true;
const bool Use_Add = true;
const bool Use_Sub = true;
const bool Use_Mul = true;
const bool Use_Mod = true;
const bool Use_Div1 = false;  /* / */
const bool Use_Div2 = true;  /* // */
const bool Use_Gcd = false;
const bool Use_Neg = true;
const bool Use_Exp = true;
const bool Use_Parens = true;

const bool CStyleMod = false;
const bool ReuseVars = true;
const bool UseAllVars = true;
const bool AllowConsts = false; // Allow const exprs e.g: 3+2, x+3+2, 3-x-2 ...

// ---- end of parameters ----

Vec py_mod(Vec a, Vec b) {
  return (a % b + b) % b;
}

Vec py_div(Vec a, Vec b) {
  return (a - py_mod(a, b)) / b;
}

value_t ipow(value_t b, value_t e) {
  value_t r = 1;
  while (e) { if (e&1) r*=b; e>>=1; b*=b; }
  return r;
}

Vec ipow(Vec b, Vec e) {
  Vec r = b;
  for (auto i=0; i<b.size(); i++) r[i] = ipow(b[i], e[i]);
  return r;
}

bool ipow_overflow(Vec b, Vec e) {
  for (int i=0; i<b.size(); i++)
    if (std::log2(std::abs(b[i])) * e[i] > sizeof(value_t) * 8 - 1)
      return true;
  return false;
}

Vec gcd(Vec a, Vec b) {
  Vec r = b;
  for (auto i=0; i<b.size(); i++) r[i] = std::gcd(a[i], b[i]);
  return r;
}

enum class Operator : uint8_t {
  Or = 0x30,
  SpaceOr = 0x31,
  OrSpace = 0x32,
  SpaceOrSpace = 0x33,
  Lt = 0x50,
  Leq = 0x51,
  Gt = 0x52,
  Geq = 0x53,
  Eq = 0x54,
  Neq = 0x55,
  BitOr = 0x60,
  BitXor = 0x70,
  BitAnd = 0x80,
  BitShl = 0x90,
  BitShr = 0x91,
  Add = 0xA0,
  Sub = 0xA1,
  Mul = 0xB0,
  Mod = 0xB1,
  Div1 = 0xB2,
  Div2 = 0xB3,
  Gcd = 0xB4, // doesn't exist in python
  Neg = 0xC0,
  BitNeg = 0xC1,
  Exp = 0xD0,
  Parens = 0xE0,
  Literal = 0xF0,
  Variable = 0xF1
};

void print_operator(Operator op) {
  switch (op) {
    case Operator::Or: printf("or"); break;
    case Operator::SpaceOr: printf(" or"); break;
    case Operator::OrSpace: printf("or "); break;
    case Operator::SpaceOrSpace: printf(" or "); break;
    case Operator::Lt: printf("<"); break;
    case Operator::Leq: printf("<="); break;
    case Operator::Gt: printf(">"); break;
    case Operator::Geq: printf(">="); break;
    case Operator::Eq: printf("=="); break;
    case Operator::Neq: printf("!="); break;
    case Operator::BitOr: printf("|"); break;
    case Operator::BitXor: printf("^"); break;
    case Operator::BitAnd: printf("&"); break;
    case Operator::BitShl: printf("<<"); break;
    case Operator::BitShr: printf(">>"); break;
    case Operator::Add: printf("+"); break;
    case Operator::Sub: printf("-"); break;
    case Operator::Mul: printf("*"); break;
    case Operator::Mod: putchar('%'); break;
    case Operator::Div1: printf("/"); break;
    case Operator::Div2: printf("//"); break;
    case Operator::Gcd: printf("∨"); break;
    case Operator::Neg: printf("-"); break;
    case Operator::BitNeg: printf("~"); break;
    case Operator::Exp: printf("**"); break;
    case Operator::Parens: printf("("); break;
    default: break;
  }
}

int operator_prec(Operator op) {
  return static_cast<int>(op) >> 4;
}

struct Expr {
  const Expr *left;
  const Expr *right;
  Operator op;
  Vec output;
  value_t literal;
  uint8_t var_mask;
  int prec() const { return operator_prec(op); }
  int used_vars() const { return std::bitset<num_vars>(var_mask).count(); }
  int unused_vars() const { return num_vars - used_vars(); }
  bool uses_all_vars() const { return unused_vars() == 0; }
};

void print_expression(const Expr *expr) {
  if (expr->left != nullptr) {
    print_expression(expr->left);
  }
  print_operator(expr->op);
  if (expr->right != nullptr) {
    print_expression(expr->right);
    if (expr->prec() == 14) {
      putchar(')');
    }
  } else if (expr->op == Operator::Variable) {
    printf("%s", inputs[expr->literal].name);
  } else {
    std::cout << expr->literal;
  }
}

struct ExprHasher {
  std::size_t operator()(const Expr &expr) const {
    std::size_t h = 0;
    for (const auto x : expr.output)
      h ^= x + 0x9e3779b9 + (h << 6) + (x >> 2);
    return h;
  }
};

struct ExprEqual {
  bool operator()(const Expr &e1, const Expr &e2) const {
    return (e1.output == e2.output).min();
  }
};

// cache[length][output] = highest-prec expression of that length yielding that output
using CacheLevel = std::unordered_set<Expr, ExprHasher, ExprEqual>;
static CacheLevel cache[max_length+1];

// "3or" and ")or" are valid, but "nor" isn't.
bool ok_before_keyword(const Expr *e) {
  if (e->right == nullptr) {
    return e->op == Operator::Literal;
  } else {
    return e->op == Operator::Parens || ok_before_keyword(e->right);
  }
}

// "or3", "orn" are invalid. Need a unary op or parens.
bool ok_after_keyword(const Expr *e) {
  if (e->left == nullptr) {
    return e->prec() != 15;
  } else {
    return ok_after_keyword(e->left);
  }
}

int positive_integer_length(int k) {
  int l = 1;
  while (k >= 10) k /= 10, l++;
  return l;
}

void validate_expression(const Expr& expr) {
  if (UseAllVars && !expr.uses_all_vars()) return;
  for (auto goal: goals) {
    if ((expr.output == goal).min()) {
      #pragma omp critical
      {
        print_expression(&expr);
        puts("");
      }
    }
  }
}

void find_expressions_left(const Expr &eR, int eR_length, int length);
void find_expressions_right(const Expr &eL, int eL_length, int length);
void cache_if_better(const Expr& expr, int length) {
  if (length == max_length || length == max_length - 1 && expr.prec() < 12) {
    validate_expression(expr);
    return;
  }

  bool found_cached_output = false;
  if (length - 1 <= max_cache_length) {
    auto el = cache[length-1].find(expr);
    if (el != cache[length-1].end()) {
      found_cached_output = true;
      if (expr.prec() <= el->prec())
        return;
    }
  }

  if (expr.left != nullptr && expr.right != nullptr) {
    if (!AllowConsts && (expr.output == expr.output[0]).min())
      return;

    if (!ReuseVars && expr.uses_all_vars()) {
      std::unordered_map<int, int> mp;
      for (int i = 0; i < expr.output.size(); i++) {
        const auto [it, emplaced] = mp.try_emplace(expr.output[i], goals[0][i]);
        if (!emplaced && it->second != goals[0][i])
          return;
      }
    }
  }

  if (length > max_cache_length) {
    if (!found_cached_output)
      validate_expression(expr);
    for (int target_length = length + 1; target_length <= max_length; target_length++) {
      find_expressions_left(expr, length, target_length);
      find_expressions_right(expr, length, target_length);
    }
    return;
  }

  #pragma omp critical
  {
    bool is_better = true;
    auto el = cache[length].find(expr);
    if (el != cache[length].end()) {
      found_cached_output = true;
      if (expr.prec() <= el->prec()) is_better = false;
      else cache[length].erase(el);
    }
    if (is_better)
      cache[length].insert(expr);
  }

  if (!found_cached_output)
    validate_expression(expr);
}

bool can_apply_operator(const Expr& left, const Expr& right, Operator op) {
  const int prec = operator_prec(op);

  if (left.prec() != prec) {
    if (left.var_mask < right.var_mask || left.var_mask == right.var_mask && &left < &right)
      if (prec == 6 || prec == 7 || prec == 8 || op == Operator::Add || op == Operator::Mul)
        return false;
    return true;
  }

  if (AllowConsts)
    return true;
  
  if (left.right != nullptr && left.right->var_mask == 0 && right.var_mask == 0) {
    if (prec == 6 || prec == 7 || prec == 8 || prec == 10)
      return false;

    if (
      left.op == op &&
      (op == Operator::Mul || op == Operator::Div1 || op == Operator::Div2)
    )
      return false;
  }

  if (left.left != nullptr && left.left->var_mask == 0 && right.var_mask == 0) {
    if (left.op == Operator::Sub)
      return false;
  }
  
  return true;
}

bool can_use_all_vars(uint8_t mask, int length) {
  const int unused_vars = num_vars - std::bitset<num_vars>(mask).count();
  return length + 2 * unused_vars <= max_length;
}

void find_1byte_operators(const Expr &eL, const Expr &eR, int length) {
  Vec z;
  if (!ReuseVars && (eL.var_mask & eR.var_mask)) return;
  const uint8_t mask = eL.var_mask | eR.var_mask;
  if (!AllowConsts && mask == 0) return;
  if (UseAllVars && !can_use_all_vars(mask, length)) return;
  if (Use_Lt && eL.prec() >= 5 && eR.prec() > 5) {
    if (eL.prec() == 5) {
      z = eL.output; z[eL.right->output >= eR.output] = 0;
    } else {
      z = 0*eL.output; z[eL.output < eR.output] = 1;
    }
    cache_if_better(Expr{&eL, &eR, Operator::Lt, z, 0, mask}, length);
  }
  if (Use_BitOr && eL.prec() >= 6 && eR.prec() > 6 && can_apply_operator(eL, eR, Operator::BitOr)) {
    cache_if_better(Expr{&eL, &eR, Operator::BitOr, eL.output | eR.output, 0, mask}, length);
  }
  if (Use_BitXor && eL.prec() >= 7 && eR.prec() > 7 && can_apply_operator(eL, eR, Operator::BitXor)) {
    cache_if_better(Expr{&eL, &eR, Operator::BitXor, eL.output ^ eR.output, 0, mask}, length);
  }
  if (Use_BitAnd && eL.prec() >= 8 && eR.prec() > 8 && can_apply_operator(eL, eR, Operator::BitAnd)) {
    cache_if_better(Expr{&eL, &eR, Operator::BitAnd, eL.output & eR.output, 0, mask}, length);
  }
  if (eL.prec() >= 10 && eR.prec() > 10) {
    if (Use_Add && can_apply_operator(eL, eR, Operator::Add))
      cache_if_better(Expr{&eL, &eR, Operator::Add, eL.output + eR.output, 0, mask}, length);
    if (Use_Sub && can_apply_operator(eL, eR, Operator::Sub))
      cache_if_better(Expr{&eL, &eR, Operator::Sub, eL.output - eR.output, 0, mask}, length);
  }
  if (eL.prec() >= 11 && eR.prec() > 11) {
    if (Use_Mul && can_apply_operator(eL, eR, Operator::Mul))
      cache_if_better(Expr{&eL, &eR, Operator::Mul, eL.output * eR.output, 0, mask}, length);
    if ((eR.output != 0 && (eL.output != int_min || eR.output != -1)).min()) {
      if (CStyleMod) {
        if (Use_Mod) cache_if_better(Expr{&eL, &eR, Operator::Mod, eL.output % eR.output, 0, mask}, length);
        if (Use_Div1 && can_apply_operator(eL, eR, Operator::Div1))
          cache_if_better(Expr{&eL, &eR, Operator::Div1, eL.output / eR.output, 0, mask}, length);
      } else {
        auto mod = py_mod(eL.output, eR.output);
        if (Use_Mod) cache_if_better(Expr{&eL, &eR, Operator::Mod, mod, 0, mask}, length);
        if (Use_Div1 && can_apply_operator(eL, eR, Operator::Div1))
          cache_if_better(Expr{&eL, &eR, Operator::Div1, (eL.output - mod) / eR.output, 0, mask}, length);
      }
    }
    if (Use_Gcd) cache_if_better(Expr{&eL, &eR, Operator::Gcd, gcd(eL.output, eR.output), 0, mask}, length);
  }
}

void find_2byte_operators(const Expr &eL, const Expr &eR, int length) {
  Vec z;
  if (!ReuseVars && (eL.var_mask & eR.var_mask)) return;
  const uint8_t mask = eL.var_mask | eR.var_mask;
  if (!AllowConsts && mask == 0) return;
  if (UseAllVars && !can_use_all_vars(mask, length)) return;
  if (eL.prec() >= 3 && eR.prec() > 3) {
    if (Use_Or && ok_before_keyword(&eL) && ok_after_keyword(&eR)) {
      z = 0*eL.output; z[eL.output == 0] = 1;
      cache_if_better(Expr{&eL, &eR, Operator::Or, eL.output + eR.output * z, 0, mask}, length);
    }
  }
  if (Use_Leq && eL.prec() >= 5 && eR.prec() > 5) {
    if (eL.prec() == 5) {
      z = eL.output; z[eL.right->output > eR.output] = 0;
    } else {
      z = 0*eL.output; z[eL.output <= eR.output] = 1;
    }
    cache_if_better(Expr{&eL, &eR, Operator::Leq, z, 0, mask}, length);
  }
  if (eL.prec() >= 9 && eR.prec() > 9 && (eR.output >= 0).min() && (eR.output <= sizeof(value_t) * 8 - 1).min()) {
    if (Use_BitShl) cache_if_better(Expr{&eL, &eR, Operator::BitShl, eL.output << eR.output, 0, mask}, length);
    if (Use_BitShr) cache_if_better(Expr{&eL, &eR, Operator::BitShr, eL.output >> eR.output, 0, mask}, length);
  }
  if (eL.prec() >= 11 && eR.prec() > 11) {
    if ((eR.output != 0 && (eL.output != int_min || eR.output != -1)).min()) {
      if (CStyleMod) {
        if (Use_Div2 && can_apply_operator(eL, eR, Operator::Div2))
          cache_if_better(Expr{&eL, &eR, Operator::Div2, eL.output / eR.output, 0, mask}, length);
      } else {
        if (Use_Div2 && can_apply_operator(eL, eR, Operator::Div2))
          cache_if_better(Expr{&eL, &eR, Operator::Div2, py_div(eL.output, eR.output), 0, mask}, length);
      }
    }
  }
  if (eL.prec() > 13 && eR.prec() >= 13 && (eR.output >= 0).min() && !ipow_overflow(eL.output, eR.output)) {
    if (Use_Exp) cache_if_better(Expr{&eL, &eR, Operator::Exp, ipow(eL.output, eR.output), 0, mask}, length);
  }
}

void find_3byte_operators(const Expr &eL, const Expr &eR, int length) {
  Vec z;
  if (!ReuseVars && (eL.var_mask & eR.var_mask)) return;
  const uint8_t mask = eL.var_mask | eR.var_mask;
  if (!AllowConsts && mask == 0) return;
  if (UseAllVars && !can_use_all_vars(mask, length)) return;
  if (eL.prec() >= 3 && eR.prec() > 3) {
    if (Use_Or) {
      z = 0*eL.output, z[eL.output == 0] = 1;
      z = eL.output + eR.output * z;
      if (!ok_before_keyword(&eL) && ok_after_keyword(&eR))
        cache_if_better(Expr{&eL, &eR, Operator::SpaceOr, z, 0, mask}, length);
      else if (ok_before_keyword(&eL) && !ok_after_keyword(&eR))
        cache_if_better(Expr{&eL, &eR, Operator::OrSpace, z, 0, mask}, length);;
    }
  }
}

void find_expressions_left(const Expr &eR, int eR_length, int length) {
  const int missing_length = length - eR_length;
  // unary operators
  if (missing_length == 1) {
    if (eR.prec() >= 12) {
      if (UseAllVars && !can_use_all_vars(eR.var_mask, length)) return;
      if (Use_BitNeg && eR.op != Operator::BitNeg) cache_if_better(Expr{nullptr, &eR, Operator::BitNeg, ~eR.output, 0, eR.var_mask}, length);
      if (Use_Neg && eR.op != Operator::Neg) cache_if_better(Expr{nullptr, &eR, Operator::Neg, -eR.output, 0, eR.var_mask}, length);
    }
    return;
  }
  // 1-byte operators
  for (const auto &eL : cache[missing_length - 1]) {
    find_1byte_operators(eL, eR, length);
  }
  // parens
  if (missing_length == 2) {
    if (UseAllVars && !can_use_all_vars(eR.var_mask, length)) return;
    if (Use_Parens && eR.prec() < 14 && max_length != length) {
      cache_if_better(Expr{nullptr, &eR, Operator::Parens, eR.output, 0, eR.var_mask}, length);
    }
    return;
  }
  // 2-byte operators
  for (const auto &eL : cache[missing_length - 2]) {
    find_2byte_operators(eL, eR, length);
  }
  // 3-byte operators
  if (missing_length == 3) return;
  for (const auto &eL : cache[missing_length - 3]) {
    find_3byte_operators(eL, eR, length);
  }
}

void find_expressions_right(const Expr &eL, int eL_length, int length) {
  const int missing_length = length - eL_length;
  // 1-byte operators
  if (missing_length == 1) return;
  for (const auto &eR : cache[missing_length - 1]) {
    find_1byte_operators(eL, eR, length);
  }
  // 2-byte operators
  if (missing_length == 2) return;
  for (const auto &eR : cache[missing_length - 2]) {
    find_2byte_operators(eL, eR, length);
  }
  // 3-byte operators
  if (missing_length == 3) return;
  for (const auto &eR : cache[missing_length - 3]) {
    find_3byte_operators(eL, eR, length);
  }
}

void find_expressions(int length) {
  if (length == 1) {
    for (value_t i = 0; i < num_vars; i++) {
      cache_if_better(Expr{nullptr, nullptr, Operator::Variable, inputs[i].vec, i, (uint8_t)(1 << i)}, length);
    }
  }
  for (const auto l : literals) {
    if (positive_integer_length(l) == length)
      cache_if_better(Expr{nullptr, nullptr, Operator::Literal, 0 * goals[0] + l, l}, length);
  }
  #if use_literals_range
    for (value_t l=min_literal; l<=max_literal; l++) {
      if (positive_integer_length(l) == length)
        cache_if_better(Expr{nullptr, nullptr, Operator::Literal, 0 * goals[0] + l, l}, length);
    }
  #endif
  #pragma omp parallel
  {
    #pragma omp single nowait
    {
      for (int eR_length = 1; eR_length < length; eR_length++) {
        for (auto it = cache[eR_length].begin(); it != cache[eR_length].end(); ++it) {
          #pragma omp task
          {
            find_expressions_left(*it, eR_length, length);
          }
        }
      }
    }
  }
}

int main() {
  printf("sizeof(Expr) = %zu\n", sizeof(Expr));
  for (int length = 1; length <= max_length; length++) {
    if (length <= max_cache_length)
      printf("Finding length %d...\n", length);
    else if (length == max_cache_length + 1)
      printf("Finding lengths %d-%d...\n", length, max_length);
    find_expressions(length);
    if (length <= max_cache_length)
      printf("Cached %zu expressions.\n", cache[length].size());
  }
  return 0;
}