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
    Fr c0, c1, av, aw, a0, a1;
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
        // pre-computed values
        Fr skC_inverse;
        GT e_pk_pkI_x0;     // for obtain
    public:
        pkC_t pkC;

    void        NIATClientKeyGen();
    bool        NIZKVerify(pkI_t& pkI, const G1& R, const G1& S, nizkpf pi);
    niat_token  NIATObtain(pkI_t& pkI, niat_psig& psig, bool eqVerified = false);
    // with batching
    // bool        NIATClientBatchedEQVerify(pkI_t& pkI, vector<eq_msg>& m, vector<eq_sig>& s);
    // bool        NIATClientBatchedPsigVerify(pkI_t& pkI, vector<niat_psig>& psigs);
    void        precompute();
    bool        NIATClientEQVerify(pkI_t& pkI, eq_msg& m, eq_sig& s);
};

class NIATIssuer {
    private:
        struct skI_t {
            std::array<Fr,2> x;
            std::array<Fr,2> y;     // for SPS-EQ
        } skI;
        GT e_g1_X0;
    public:
        pkI_t pkI;

    void        NIATIssuerKeyGen();
    niat_psig   NIATIssue(const pkC_t& pkC, int b);
    nizkpf      NIZKProve(const G1& R, const G1& S, const int b);
    int         NIATReadBit(niat_token& token, bool eqVerified = false);
    // with batching
    // bool        NIATIssuerBatchedVerify(vector<niat_token>& tokens);
    void        precompute();       // TODO, this opens up a whole can of worms..
    bool        NIATIssuerEQVerify(eq_msg& m, eq_sig& s);
};

/* ------------------------------- utils ------------------------------- */

void HashtoG1(G1& X, const std::string& x) { Fp tmp; tmp.setHashOf(x); mapToG1(X, tmp); }

/*
 * Public verification algorithm for the _final_ tokens.
 * Anyone can call this given any public keys and any tokens.
 */
bool NIATPublicVerify(pkI_t& pkI, niat_token& token);

#endif /* _NIAT_H */
