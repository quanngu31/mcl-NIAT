#ifndef _NIAT_H
#define _NIAT_H

#include <mcl/bls12_381.hpp>
#include <vector>

using namespace mcl::bn;
using std::vector;

/* ----------------------------------------------------------------------- */
// EQ signatures
const int EQ_SIZE = 3;
typedef std::array<Fr, EQ_SIZE> eq_sk;
typedef std::array<G2, EQ_SIZE> eq_pk;

typedef std::array<G1, EQ_SIZE> eq_msg;
typedef std::array<G1, 2> niat_tag;
struct eq_sig
{
    G1 Z, Y1;
    G2 Y2;
};

void    EQKeyGen(eq_sk &sk, eq_pk &pk);
eq_sig  EQSign(const eq_sk &sk, const eq_msg &m);
bool    EQVerify(const eq_pk &pk, const eq_msg &m, const eq_sig &s);
eq_sig  EQChRep(const eq_sig &s, const Fr &mu);

/* ----------------------------------------------------------------------- */

struct nizkpf
{
    Fr c0, c1, au, av, aw, a0, a1;
};

struct niat_psig
{
    eq_sig sig;
    G1 S;
    nizkpf pi;
    std::string nonce;
};

struct niat_token
{
    niat_tag tag;
    eq_sig sig;
};

// public values are defined in global scope,
// otherwise we run into a mess of circular dependency
typedef G1 pkC_t;
struct pkI_t
{
    std::array<G1, 2> X;
    std::array<G2, 3> Y; // for SPS-EQ
};

/* ----------------------------------------------------------------------- */
// NIAT Protocol
class NIATClient
{
private:
    Fr skC;
    Fr skC_inverse;
    GT eC; // pre-computable, e(pkC, pkI^(3)) in paper
    // note that this is specific to an Issuer, so it might be better
    // to model as an `unordered_map <pkI, precomputed eC>`
public:
    pkC_t pkC;

    void NIATClientKeyGen();
    void precompute(const pkI_t &pkI);
    bool NIZKVerify(const pkI_t &pkI, const G1 &R, const G1 &S, nizkpf pi);
    niat_token NIATObtain(const pkI_t &pkI, niat_psig &psig);
    niat_token NIATObtainWrapper(const pkI_t &pkI, niat_psig &psig);

    bool NIATClientVerify(const pkI_t &pkI, niat_psig &psig);
    bool NIATClientBatchVerify(const pkI_t &pkI, vector<niat_psig> &psigs);
};

class NIATIssuer
{
private:
    struct skI_t
    {
        std::array<Fr, 2> x;
        std::array<Fr, 3> y; // for SPS-EQ
    } skI;
    GT eI; // pre-computable, e(g1, pkI^(3)) in paper
public:
    pkI_t pkI;

    void NIATIssuerKeyGen();
    void precompute();
    niat_psig NIATIssue(const pkC_t &pkC, int b);
    nizkpf NIZKProve(const G1 &R, const G1 &S, const int b);
    int NIATReadBit(niat_token &token);

    bool NIATIssuerVerify(niat_token &token);
    bool NIATIssuerBatchVerify(vector<niat_token> &tokens);
};

// utils
inline void HashtoG1(G1 &X, const std::string &x)
{
    Fp tmp;
    tmp.setHashOf(x);
    mapToG1(X, tmp);
}

/* --------------------------- Optimization  -------------------------------
 * Optimizations specific to the NIAT protocol
 * -------------------------------------------------------------------------*/

bool EQVerify(const eq_pk &pk, const eq_msg &m, const eq_sig &s, const GT &ePrecomputed);
bool EQBatchVerify(const eq_pk &pk, const vector<eq_msg> &msgs, const vector<eq_sig> &sigs, const GT &ePrecomputed);

#endif /* _NIAT_H */
