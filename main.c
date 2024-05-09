/**
 * Песочница для экспериментов с программной эмуляцией плавающей точки (IEEE 754).
 *
 * За основу взяты следующие программные реализации:
 * - clang (https://github.com/llvm/llvm-project).
 * - softfp (https://bellard.org/softfp/).
 *
 * Для простоты убрана поддержка спец. значений и денормализованных чисел.
 */

#include <stdio.h>
#include <stdlib.h>

#include <stdbool.h>
#include <inttypes.h>
#include <assert.h>

// clang
#define clzsi __builtin_clz
#define implicitBit (REP_C(1) << significandBits)
#define significandMask (implicitBit - 1U)
#define REP_C UINT32_C
#define significandBits 23
#define typeWidth (sizeof(uint32_t) * CHAR_BIT)
#define exponentBits (typeWidth - significandBits - 1)
#define maxExponent ((1 << exponentBits) - 1)
#define signBit (REP_C(1) << (significandBits + exponentBits))

#define absMask (signBit - 1U)

typedef uint32_t rep_t;

static __inline int rep_clz(rep_t a)
{
    return clzsi(a);
}
rep_t f_add(uint32_t a, uint32_t b);
int normalize(rep_t *significand);
// END clang

// SoftFP
#define F_SIZE 32
#define F_UINT uint32_t
#define MANT_MASK (((F_UINT)1 << MANT_SIZE) - 1)
#define MANT_SIZE 23
#define EXP_MASK ((1 << EXP_SIZE) - 1)
#define EXP_SIZE 8
#define FFLAG_INVALID_OP  (1 << 4)

#define xglue(x, y) x ## y
#define glue(x, y) xglue(x, y)

#define F_QNAN glue(F_QNAN, F_SIZE)

#define FFLAG_DIVIDE_ZERO (1 << 3)

#define isnan_sf glue(isnan_sf, F_SIZE)
#define issignan_sf glue(issignan_sf, F_SIZE)

#define pack_sf glue(pack_sf, F_SIZE)

static inline F_UINT pack_sf(uint32_t a_sign, uint32_t a_exp, F_UINT a_mant)
{
    return ((F_UINT)a_sign << (F_SIZE - 1)) |
        ((F_UINT)a_exp << MANT_SIZE) |
        (a_mant & MANT_MASK);
}

#define normalize_subnormal_sf glue(normalize_subnormal_sf, F_SIZE)

#define RND_SIZE (IMANT_SIZE - MANT_SIZE)
#define FFLAG_INEXACT     (1 << 0)

#define divrem_u glue(divrem_u, F_SIZE)

#define F_ULONG uint64_t

#define normalize_sf glue(normalize_sf, F_SIZE)

#define IMANT_SIZE (F_SIZE - 2) /* internal mantissa size */

#define round_pack_sf glue(roundpack_sf, F_SIZE)

#define FFLAG_UNDERFLOW   (1 << 1)
#define FFLAG_OVERFLOW    (1 << 2)

static inline int clz32(uint32_t a)
{
    int r;
    if (a == 0) {
        r = 32;
    } else {
        r = __builtin_clz(a);
    }
    return r;
}

#define clz glue(clz, F_SIZE)

#define rshift_rnd glue(rshift_rnd, F_SIZE)

static const F_UINT F_QNAN = (((F_UINT)EXP_MASK << MANT_SIZE) | ((F_UINT)1 << (MANT_SIZE - 1)));

static F_UINT rshift_rnd(F_UINT a, int d)
{
    F_UINT mask;
    if (d != 0) {
        if (d >= F_SIZE) {
            a = (a != 0);
        } else {
            mask = ((F_UINT)1 << d) - 1;
            a = (a >> d) | ((a & mask) != 0);
        }
    }
    return a;
}

typedef enum {
    RM_RNE, /* Round to Nearest, ties to Even */
    RM_RTZ, /* Round towards Zero */
    RM_RDN, /* Round Down */
    RM_RUP, /* Round Up */
    RM_RMM, /* Round to Nearest, ties to Max Magnitude */
} RoundingModeEnum;

typedef int BOOL;
enum {
    FALSE = 0,
    TRUE = 1,
};

/* a_mant is considered to have its MSB at F_SIZE - 2 bits */
static F_UINT round_pack_sf(uint32_t a_sign, int a_exp, F_UINT a_mant,
                            RoundingModeEnum rm, uint32_t *pfflags)
{
    int diff;
    uint32_t addend, rnd_bits;

    switch(rm) {
    case RM_RNE:
    case RM_RMM:
        addend = (1 << (RND_SIZE - 1));
        break;
    case RM_RTZ:
        addend = 0;
        break;
    default:
    case RM_RDN:
    case RM_RUP:
        //        printf("s=%d rm=%d m=%x\n", a_sign, rm, a_mant);
        if (a_sign ^ (rm & 1))
            addend = (1 << RND_SIZE) - 1;
        else
            addend = 0;
        break;
    }

    /* potentially subnormal */
    if (a_exp <= 0) {
        BOOL is_subnormal;
        /* Note: we set the underflow flag if the rounded result
           is subnormal and inexact */
        is_subnormal = (a_exp < 0 ||
                        (a_mant + addend) < ((F_UINT)1 << (F_SIZE - 1)));
        diff = 1 - a_exp;
        a_mant = rshift_rnd(a_mant, diff);
        rnd_bits = a_mant & ((1 << RND_SIZE ) - 1);
        if (is_subnormal && rnd_bits != 0) {
            *pfflags |= FFLAG_UNDERFLOW;
        }
        a_exp = 1;
    } else {
        rnd_bits = a_mant & ((1 << RND_SIZE ) - 1);
    }
    if (rnd_bits != 0)
        *pfflags |= FFLAG_INEXACT;
    a_mant = (a_mant + addend) >> RND_SIZE;
    /* half way: select even result */
    if (rm == RM_RNE && rnd_bits == (1 << (RND_SIZE - 1)))
        a_mant &= ~1;
    /* Note the rounding adds at least 1, so this is the maximum
       value */
    a_exp += a_mant >> (MANT_SIZE + 1);
    if (a_mant <= MANT_MASK) {
        /* denormalized or zero */
        a_exp = 0;
    } else if (a_exp >= EXP_MASK) {
        /* overflow */
        if (addend == 0) {
            a_exp = EXP_MASK - 1;
            a_mant = MANT_MASK;
        } else {
            /* infinity */
            a_exp = EXP_MASK;
            a_mant = 0;
        }
        *pfflags |= FFLAG_OVERFLOW | FFLAG_INEXACT;
    }
    return pack_sf(a_sign, a_exp, a_mant);
}

/* a_mant is considered to have at most F_SIZE - 1 bits */
static F_UINT normalize_sf(uint32_t a_sign, int a_exp, F_UINT a_mant,
                           RoundingModeEnum rm, uint32_t *pfflags)
{
    int shift;
    shift = clz(a_mant) - (F_SIZE - 1 - IMANT_SIZE);
    assert(shift >= 0);
    a_exp -= shift;
    a_mant <<= shift;
    return round_pack_sf(a_sign, a_exp, a_mant, rm, pfflags);
}

static F_UINT divrem_u(F_UINT *pr, F_UINT ah, F_UINT al, F_UINT b)
{
    F_ULONG a;
    a = ((F_ULONG)ah << F_SIZE) | al;
    *pr = a % b;
    return a / b;
}

BOOL isnan_sf(F_UINT a)
{
    uint32_t a_exp;
    F_UINT a_mant;
    a_exp = (a >> MANT_SIZE) & EXP_MASK;
    a_mant = a & MANT_MASK;
    return (a_exp == EXP_MASK && a_mant != 0);
}

BOOL issignan_sf(F_UINT a)
{
    uint32_t a_exp1;
    F_UINT a_mant;
    a_exp1 = (a >> (MANT_SIZE - 1)) & ((1 << (EXP_SIZE + 1)) - 1);
    a_mant = a & MANT_MASK;
    return (a_exp1 == (2 * EXP_MASK) && a_mant != 0);
}

static inline F_UINT normalize_subnormal_sf(int32_t *pa_exp, F_UINT a_mant)
{
    int shift;
    shift = MANT_SIZE - ((F_SIZE - 1 - clz(a_mant)));
    *pa_exp = 1 - shift;
    return a_mant << shift;
}

F_UINT div_sf(F_UINT a, F_UINT b, RoundingModeEnum rm, uint32_t *pfflags);
// End SoftFP

void test_add();
void test_div();

int main()
{
    // test_add();
    test_div();

    return 0;
}

/**
 * Floating-Point multiplication.
 *
 * В clang вычисляется точное произведение (в двойной разрядной сетке) и затем выполняется корректное округление до одинарной точности.
 * В SoftFloat тоже вычисляется произведение в двойной сетке, но округление происходит по принципу отличному (по крайней мере внешне) от clang.
 *
 * У меня получилось собственное решение, в исходной разрядной сетке (по схеме со стики-битом), поэтому здесь я не разбирал ни одну из сишных реализаций.
 */

/**
 * Floating-Point division (SoftFP).
 *
 * В clang и SoftFloat деление реализовано методом Ньютона-Рафсона (итеративным приближением величины обратной делителю) поэтому здесь не рассматривается.
 */
void test_div()
{
    uint32_t fflags = 0;

    F_UINT a, b;
    F_UINT res;

    //a = 0x3f000000; // 0.5
    //b = 0x7f7fffff; // 340282346638528859811704183484516925440

    //a = 0x01696b3d; // 1.82358515262603759765625 * 2^-125
    //b = 0x3f0c61ff; // 1.09674060344696044921875 * 2^-1

    a = 0x3f800000; // 1.0f.
    b = 0x3fffffff; // 1.99999988079071044921875f.
    res = div_sf(a, b, RM_RNE, &fflags);
    assert(res == 0x3f000001);

    // Денормализованное частное.
    a = 0x05d82220; // 1.688541412353515625f * powl(2, -116).
    b = 0x49812200; // 1.00885009765625f * powl(2, 20).
    res = div_sf(a, b, RM_RNE, &fflags);
    assert(res == 0x0000358f);
}

F_UINT div_sf(F_UINT a, F_UINT b, RoundingModeEnum rm, uint32_t *pfflags)
{
    uint32_t a_sign, b_sign, r_sign;
    int32_t a_exp, b_exp, r_exp;
    F_UINT a_mant, b_mant, r_mant, r;

    a_sign = a >> (F_SIZE - 1);
    b_sign = b >> (F_SIZE - 1);
    r_sign = a_sign ^ b_sign;

    a_exp = (a >> MANT_SIZE) & EXP_MASK;
    b_exp = (b >> MANT_SIZE) & EXP_MASK;
    a_mant = a & MANT_MASK;
    b_mant = b & MANT_MASK;
    if (a_exp == EXP_MASK)
    {
        if (a_mant != 0 || isnan_sf(b))
        {
            if (issignan_sf(a) || issignan_sf(b))
            {
                *pfflags |= FFLAG_INVALID_OP;
            }
            return F_QNAN;
        }
        else if (b_exp == EXP_MASK)
        {
            *pfflags |= FFLAG_INVALID_OP;
            return F_QNAN;
        }
        else
        {
            return pack_sf(r_sign, EXP_MASK, 0);
        }
    }
    else if (b_exp == EXP_MASK)
    {
        if (b_mant != 0)
        {
            if (issignan_sf(a) || issignan_sf(b))
            {
                *pfflags |= FFLAG_INVALID_OP;
            }
            return F_QNAN;
        }
        else
        {
            return pack_sf(r_sign, 0, 0);
        }
    }

    if (b_exp == 0)
    {
        if (b_mant == 0)
        {
            /* zero */
            if (a_exp == 0 && a_mant == 0)
            {
                *pfflags |= FFLAG_INVALID_OP;
                return F_QNAN;
            }
            else
            {
                *pfflags |= FFLAG_DIVIDE_ZERO;
                return pack_sf(r_sign, EXP_MASK, 0);
            }
        }
        b_mant = normalize_subnormal_sf(&b_exp, b_mant);
    }
    else
    {
        b_mant |= (F_UINT)1 << MANT_SIZE;
    }
    if (a_exp == 0)
    {
        if (a_mant == 0)
            return pack_sf(r_sign, 0, 0); /* zero */
        a_mant = normalize_subnormal_sf(&a_exp, a_mant);
    }
    else
    {
        a_mant |= (F_UINT)1 << MANT_SIZE;
    }
    r_exp = a_exp - b_exp + (1 << (EXP_SIZE - 1)) - 1;
    r_mant = divrem_u(&r, a_mant, 0, b_mant << 2);
    if (r != 0)
        r_mant |= 1;
    return normalize_sf(r_sign, r_exp, r_mant, rm, pfflags);
}

/**
 * Floating-Point addition (clang).
 */
void test_add()
{
    rep_t a, b;
    rep_t res;

//================================================================
// Zeroes
//================================================================
    a = 0x80000000; // -0
    b = 0x80000000; // -0
    res = f_add(a, b);
    assert(res == 0x80000000);

    a = 0x80000000; // -0
    b = 0x00000000; // +0
    res = f_add(a, b);
    assert(res == 0x00000000);

    a = 0x00000000; // +0
    b = 0x80000000; // -0
    res = f_add(a, b);
    assert(res == 0x00000000);

    a = 0x00000000; // +0
    b = 0x00000000; // +0
    res = f_add(a, b);
    assert(res == 0x00000000);

    a = 0x3f000000; // 0.5
    b = 0x00000000; // 0
    res = f_add(a, b);
    assert(res == a);

    a = 0x00000000; // 0
    b = 0x3f000000; // 0.5
    res = f_add(a, b);
    assert(res == b);

//================================================================
//
//================================================================
    a = 0x3dcccccd; // 0.1
    b = 0x3f000000; // 0.5
    res = f_add(a, b);

//================================================================
// Exponent alignment
//================================================================
    a = 0x3f800001; // 1.00000011920928955078125
    b = 0x33800000; // 2^-24
    res = f_add(a, b);

    a = 0x3f800001; // 1.00000011920928955078125
    b = 0x32000000; // 2^-27
    res = f_add(a, b);

    a = 0x3f800001; // 1.00000011920928955078125
    b = 0x2f800000; // 2^-32
    res = f_add(a, b);

//================================================================
// Subtraction.
//
// Sticky-bit is set for b,
// is not equal true bit in this position.
//
// Preliminary result is denormal.
// True result = 0.937499992549419403076171875
//================================================================
    a = 0x3f800000; // 1
    b = 0xbd800001; // -0.062500007450580596923828125
    res = f_add(a, b);
}

rep_t f_add(rep_t aRep, rep_t bRep)
{
    const rep_t aAbs = aRep & absMask;
    const rep_t bAbs = bRep & absMask;

    /* Спец. значения пока не реализуем.
    // Detect if a or b is zero, infinity, or NaN.
    if (aAbs - REP_C(1) >= infRep - REP_C(1) || bAbs - REP_C(1) >= infRep - REP_C(1))
    {
        // NaN + anything = qNaN
        if (aAbs > infRep)
            return fromRep(toRep(a) | quietBit);
        // anything + NaN = qNaN
        if (bAbs > infRep)
            return fromRep(toRep(b) | quietBit);

        if (aAbs == infRep)
        {
            // +/-infinity + -/+infinity = qNaN
            if ((toRep(a) ^ toRep(b)) == signBit)
                return fromRep(qnanRep);
            // +/-infinity + anything remaining = +/- infinity
            else
                return a;
        }

        // anything remaining + +/-infinity = +/-infinity
        if (bAbs == infRep)
            return b;

        // zero + anything = anything
        if (!aAbs)
        {
            // We need to get the sign right for zero + zero.
            if (!bAbs)
                return aRep & bRep;
            else
                return bRep;
        }

        // anything + zero = anything
        if (!bAbs)
            return aRep;
    }
    */

    // zero + anything = anything
    if (!aAbs)
    {
        // We need to get the sign right for zero + zero.
        if (!bAbs)
            return aRep & bRep;
        else
            return bRep;
    }

    // anything + zero = anything
    if (!bAbs)
        return aRep;

    // Swap a and b if necessary so that a has the larger absolute value.
    if (bAbs > aAbs)
    {
        const rep_t temp = aRep;
        aRep = bRep;
        bRep = temp;
    }

    // Extract the exponent and significand from the (possibly swapped) a and b.
    int aExponent = aRep >> significandBits & maxExponent;
    int bExponent = bRep >> significandBits & maxExponent;
    rep_t aSignificand = aRep & significandMask;
    rep_t bSignificand = bRep & significandMask;

    /*
    // Normalize any denormals, and adjust the exponent accordingly.
    if (aExponent == 0)
        aExponent = normalize(&aSignificand);
    if (bExponent == 0)
        bExponent = normalize(&bSignificand);
    */

    // The sign of the result is the sign of the larger operand, a.  If they
    // have opposite signs, we are performing a subtraction.  Otherwise, we
    // perform addition.
    const rep_t resultSign = aRep & signBit;
    const bool subtraction = (aRep ^ bRep) & signBit;

    // Shift the significands to give us round, guard and sticky, and set the
    // implicit significand bit.  If we fell through from the denormal path it
    // was already set by normalize( ), but setting it twice won't hurt
    // anything.
    aSignificand = (aSignificand | implicitBit) << 3;
    bSignificand = (bSignificand | implicitBit) << 3;

    // Shift the significand of b by the difference in exponents, with a sticky
    // bottom bit to get rounding correct.
    const unsigned int align = aExponent - bExponent;
    if (align)
    {
        if (align < typeWidth)
        {
            const bool sticky = (bSignificand << (typeWidth - align)) != 0;
            bSignificand = bSignificand >> align | sticky;
        }
        else
        {
            bSignificand = 1; // Set the sticky bit.  b is known to be non-zero.
        }
    }

    if (subtraction)
    {
        aSignificand -= bSignificand;

        // If a == -b, return +zero.
        if (aSignificand == 0)
            return 0;

        // If partial cancellation occured, we need to left-shift the result
        // and adjust the exponent.
        if (aSignificand < implicitBit << 3)
        {
            const int shift = rep_clz(aSignificand) - rep_clz(implicitBit << 3);
            aSignificand <<= shift;
            aExponent -= shift;
        }
    }
    else /* addition */
    {
        aSignificand += bSignificand;

        // If the addition carried up, we need to right-shift the result and
        // adjust the exponent.
        if (aSignificand & implicitBit << 4)
        {
            const bool sticky = aSignificand & 1;
            aSignificand = aSignificand >> 1 | sticky;
            aExponent += 1;
        }
    }

    /* Со спец. значениями пока не работаем.
    // If we have overflowed the type, return +/- infinity.
    if (aExponent >= maxExponent)
        return fromRep(infRep | resultSign);
    */

    // TODO: Проверить на overflow после сложения.

    /* Денормализованные числа пока не реализуем.
    if (aExponent <= 0)
    {
        // The result is denormal before rounding.  The exponent is zero and we
        // need to shift the significand.
        const int shift = 1 - aExponent;
        const bool sticky = (aSignificand << (typeWidth - shift)) != 0;
        aSignificand = aSignificand >> shift | sticky;
        aExponent = 0;
    }
    */

    // Вместо формирования денормализованного числа возвращаем ноль.
    // Корректный знак будет установлен далее перед округлением.
    if (aExponent <= 0)
    {
        aSignificand = 0;
        aExponent = 0;
    }

    // Low three bits are round, guard, and sticky.
    const int roundGuardSticky = aSignificand & 0x7;

    // Shift the significand into place, and mask off the implicit bit.
    rep_t result = aSignificand >> 3 & significandMask;

    // Insert the exponent and sign.
    result |= (rep_t)aExponent << significandBits;
    result |= resultSign;

    /*
    // Perform the final rounding.  The result may overflow to infinity, but
    // that is the correct result in that case.
    switch (__fe_getround())
    {
    case CRT_FE_TONEAREST:
        if (roundGuardSticky > 0x4)
            result++;
        if (roundGuardSticky == 0x4)
            result += result & 1;
        break;
    case CRT_FE_DOWNWARD:
        if (resultSign && roundGuardSticky) result++;
        break;
    case CRT_FE_UPWARD:
        if (!resultSign && roundGuardSticky) result++;
        break;
    case CRT_FE_TOWARDZERO:
        break;
    }
    */

    // Округляем только к ближайшему и к четному.
    if (roundGuardSticky > 0x4)
        result++;
    if (roundGuardSticky == 0x4)
        result += result & 1;

    /*
    if (roundGuardSticky)
        __fe_raise_inexact();
    */

    // return fromRep(result);

    // TODO: Проверить на overflow после округления. Это вместо формирования inf, который мы пока не реализуем.
    return result;
}

int normalize(rep_t *significand)
{
    const int shift = rep_clz(*significand) - rep_clz(implicitBit);
    *significand <<= shift;
    return 1 - shift;
}
