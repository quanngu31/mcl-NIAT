#ifndef _NIAT_H
#define _NIAT_H

#include <mcl/bls12_381.hpp>
#include <vector>

using namespace mcl::bn;
using std::vector;

/* ----------------------------------------------------------------------- */
// EQ signatures
const int EQ_SIZE = 2;
typedef std::array<Fr,EQ_SIZE> eq_sk;
typedef std::array<G2,EQ_SIZE> eq_pk;

typedef std::array<G1,EQ_SIZE> eq_msg;
struct eq_sig {
    G1 Z, Y1;
    G2 Y2;
};

void    EQKeyGen(eq_sk& sk, eq_pk& pk);
eq_sig  EQSign(const eq_sk& sk, const eq_msg& m);
bool    EQVerify(const eq_pk& pk, const eq_msg& m, const eq_sig& s);
eq_sig  EQChRep(const eq_sig& s, const Fr& mu);

/* ----------------------------------------------------------------------- */

struct nizkpf {
    Fr c0, c1, as, a0, a1, a2;
};

struct niat_psig {
    eq_sig sig;
    G1 S;
    nizkpf pi;
    std::string nonce;
};
struct niat_token {
    eq_msg tag;
    eq_sig sig;
};

// otherwise we run into a mess of circular dependency
typedef G1 pkC_t;
struct pkI_t {
    std::array<G1,2> X;
    std::array<G2,2> Y;    // for SPS-EQ
};

class NIATClient {
    private:
        Fr skC;
    public:
        pkC_t pkC;

    void        NIATClientKeyGen();
    bool        NIATClientEQVerify(pkI_t& pkI, eq_msg& m, eq_sig& s);
    bool        NIZKVerify(pkI_t& pkI, const G1& R, const G1& S, nizkpf pi);
    niat_token  NIATObtain(pkI_t& pkI, niat_psig& psig, bool eqVerified = false);
    // with batching
    bool        NIATClientBatchedEQVerify(pkI_t& pkI, vector<eq_msg>& m, vector<eq_sig>& s);
    bool        NIATClientBatchedPsigVerify(pkI_t& pkI, vector<niat_psig>& psigs);
};

class NIATIssuer {
    private:
        struct skI_t {
            std::array<Fr,2> x;
            std::array<Fr,2> y;     // for SPS-EQ
        } skI;
    public:
        pkI_t pkI;

    void        NIATIssuerKeyGen();
    niat_psig   NIATIssue(const pkC_t& pkC, int b);
    nizkpf      NIZKProve(const G1& R, const G1& S, const int b);
    bool        NIATIssuerEQVerify(eq_msg& m, eq_sig& s);
    int         NIATReadBit(niat_token& token, bool eqVerified = false);
    // with batching
    bool        NIATIssuerBatchedVerify(vector<niat_token>& tokens);
};


class Precomputations {
    // pre-computed pairings
    Fp12 eC, e_pkCm_pkI1m;  // Client
    G1 pkC_m;
    Fp12 eI, e_g1n_pkI1n;   // Issuer
};

// utils
void HashtoG1(G1& X, const std::string& x) { Fp tmp; tmp.setHashOf(x); mapToG1(X, tmp); }

#endif /* _NIAT_H */
