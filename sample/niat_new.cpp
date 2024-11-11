/*******************************************************************************
 * This is experimental code for Non-interactive Anonymous Tokens
 * Author(s):    Quan Nguyen (@quanngu31)
 *               Aayush Yadav (@aayux)
 ********************************************************************************
 *----------------------------------- HOW TO ------------------------------------
 ********************************************************************************
 * Follow the steps below to run this file:
 *
 * 1. Clone the repo:
 * $ git clone https://github.com/aayux/mcl.git
 *
 * 2. Make the exe
 * $ make bin/niat.exe
 *
 * 3. Execute the exe
 * $ ./bin/niat.exe
 *******************************************************************************/

#include <iostream>
#include <mcl/bls12_381.hpp>
#include <ostream>
#include <string>

#include "mcl/bn.hpp"
#include "niat.h"

using namespace mcl::bn;
using std::endl;
using std::vector;

G1 P; // generator g1 of G1
G2 Q; // generator g2 of G2

#define USEDEBUG

#ifdef USEDEBUG
#define Debug(x) std::cout << x
#else
#define Debug(x)
#endif

/* ------------------------------ EQ-SPS ------------------------------ */

void EQKeyGen(eq_sk &sk, eq_pk &pk)
{
    for (int i = 0; i < EQ_SIZE; i++)
    {
        sk[i].setByCSPRNG();
        pk[i] = Q * sk[i];
    }
}

eq_sig EQSign(const eq_sk &sk, const eq_msg &m)
{
    if (m.size() != sk.size())
    {
        throw std::runtime_error("EQSign: Size of message and secret key mismatched.");
    }
    Fr nu, nu_inv;
    nu.setByCSPRNG();
    Fr::inv(nu_inv, nu);
    eq_sig s;
    s.Y1 = P * nu_inv; // Y1 = g1^(1/r)
    s.Y2 = Q * nu_inv; // Y2 = g2^(1/r)
    s.Z.clear();       // set 0 for addition
    for (int i = 0; i < EQ_SIZE; i++)
    {
        s.Z += m[i] * sk[i];
    }
    s.Z = s.Z * nu; // Z = sum(mi^xi)^nu
    return s;
}

bool EQVerify(const eq_pk &pk, const eq_msg &m, const eq_sig &s)
{
    if (m.size() != pk.size())
    {
        throw std::runtime_error("EQVerify: Size of message and public key mismatched.");
    }
    // e(g1, Y2) = e(Y1, g2)
    GT e1, e2;
    pairing(e1, P, s.Y2);
    pairing(e2, s.Y1, Q);
    // e(m1, pk1) * e(m2, pk2) = e(Z, Y2)
    GT lhs, rhs;
    millerLoopVec(lhs, m.data(), pk.data(), EQ_SIZE); // this does exactly what lhs needs
    finalExp(lhs, lhs);                               // how finalExp is used internally in the library
    pairing(rhs, s.Z, s.Y2);
    return (e1 == e2) && (lhs == rhs);
}

eq_sig EQChRep(const eq_sig &s, const Fr &mu)
{
    eq_sig s_;
    Fr psi, psi_inv;
    psi.setByCSPRNG();
    Fr::inv(psi_inv, psi);
    s_.Y1 = s.Y1 * psi_inv;  // Y1' = Y1^(1/psi)
    s_.Y2 = s.Y2 * psi_inv;  // Y2' = Y2^(1/psi)
    s_.Z = s.Z * (psi * mu); // Z'  = Z^(mu * psi)
    return s_;
}

/* Complement function for EQChRep to adapt a message for a ChRep'd signature */
static eq_msg EQAdaptMessage(const eq_msg &m, const Fr &mu)
{
    eq_msg m_;
    for (int i = 0; i < EQ_SIZE; i++)
    {
        m_[i] = m[i] * mu;
    }
    return m_;
}

/* ------------------------------ NIZK  ------------------------------ */

bool NIATClient::NIZKVerify(const pkI_t &pkI, const G1 &R, const G1 &S, nizkpf pi)
{
    // statement
    G1 U[2] = {pkI.X[0], pkI.X[1]};
    G2 V = pkI.Y[0], W = pkI.Y[1];
    // compute to verify
    G1 S_tilde[2], U_tilde[2];
    S_tilde[0] = (R * pi.a0) - (S * pi.c0);
    S_tilde[1] = (R * pi.a1) - (S * pi.c1);
    U_tilde[0] = (P * pi.a0) - (U[0] * pi.c0);
    U_tilde[1] = (P * pi.a1) - (U[1] * pi.c1);
    Fr c = pi.c0 + pi.c1;
    G2 V_tilde = (Q * pi.av) - (V * c);
    G2 W_tilde = (Q * pi.aw) - (W * c);
    // transcript
    std::ostringstream transcript;
    transcript << "<nizkproof> " << endl
               << "S_tilde[0]: " + S_tilde[0].getStr() << endl
               << "S_tilde[1]: " + S_tilde[1].getStr() << endl
               << "U_tilde[0]: " + U_tilde[0].getStr() << endl
               << "U_tilde[1]: " + U_tilde[1].getStr() << endl
               << "V_tilde:    " + V_tilde.getStr() << endl
               << "W_tilde:    " + W_tilde.getStr() << endl
               << "</nizkproof>";
    Fr c_computed;
    c_computed.setHashOf(transcript.str());
    return (c == c_computed);
}

nizkpf NIATIssuer::NIZKProve(const G1 &R, const G1 &S, const int b)
{
    // statement
    G1 U[2] = {this->pkI.X[0], this->pkI.X[1]};
    G2 V = this->pkI.Y[0], W = this->pkI.Y[1];
    // compute the proof
    Fr z[2], c[2], a[2], zv, zw;
    G1 S_tilde[2], U_tilde[2];
    // sampling
    z[b].setByCSPRNG();
    zv.setByCSPRNG();
    zw.setByCSPRNG();
    c[1 - b].setByCSPRNG();
    a[1 - b].setByCSPRNG();
    // compute
    S_tilde[b] = R * z[b];
    S_tilde[1 - b] = (R * a[1 - b]) - (S * c[1 - b]);
    U_tilde[b] = P * z[b];
    U_tilde[1 - b] = (P * a[1 - b]) - (U[1 - b] * c[1 - b]);
    G2 V_tilde = Q * zv;
    G2 W_tilde = Q * zw;
    // transcript
    std::ostringstream transcript;
    transcript << "<nizkproof> " << endl
               << "S_tilde[0]: " + S_tilde[0].getStr() << endl
               << "S_tilde[1]: " + S_tilde[1].getStr() << endl
               << "U_tilde[0]: " + U_tilde[0].getStr() << endl
               << "U_tilde[1]: " + U_tilde[1].getStr() << endl
               << "V_tilde:    " + V_tilde.getStr() << endl
               << "W_tilde:    " + W_tilde.getStr() << endl
               << "</nizkproof>";
    Fr cTotal;
    cTotal.setHashOf(transcript.str());
    // keep computing
    Fr av = zv + (cTotal * this->skI.y[0]);
    Fr aw = zw + (cTotal * this->skI.y[1]);
    c[b] = cTotal - c[1 - b];
    a[b] = z[b] + (c[b] * this->skI.x[b]);
    nizkpf pi = {
        .c0 = c[0],
        .c1 = c[1],
        .av = av,
        .aw = aw,
        .a0 = a[0],
        .a1 = a[1]};
    return pi;
}

/* ------------------------------ NIAT  ------------------------------ */

void NIATClient::NIATClientKeyGen()
{
    this->skC.setByCSPRNG();
    this->pkC = P * skC;
    Fr::inv(this->skC_inverse, this->skC); // pre-compute the inverse
}

/**
 * wrapper for EQVerify on the client side, using the precomputed e
 */
bool NIATClient::NIATClientVerify(const pkI_t &pkI, niat_psig &psig)
{
    G1 R;
    HashtoG1(R, psig.nonce);
    eq_msg m = {pkC, (psig.S + R)};
    return EQVerify(pkI.Y, m, psig.sig, this->eC);
}

/**
 * Computes the final token
 */
niat_token NIATClient::NIATObtain(const pkI_t &pkI, niat_psig &psig)
{   // assumes that the psig has been checked for validity.
    (void) pkI;
    G1 R;
    HashtoG1(R, psig.nonce);
    eq_msg _tag = {(R * this->skC_inverse), (psig.S * this->skC_inverse)}; // this is not actually a message to any EQ algorithms, but anyway..
    eq_sig _sig = EQChRep(psig.sig, this->skC_inverse);
    niat_token token = {
        .tag = _tag,
        .sig = _sig,
    };
    return token;
}

/**
 * Wraps all the steps in Obtain.
 */
niat_token NIATClient::NIATObtainWrapper(const pkI_t &pkI, niat_psig &psig)
{
    G1 R;
    HashtoG1(R, psig.nonce);
    if (NIZKVerify(pkI, R, psig.S, psig.pi) != true)
    {
        std::cerr << "NIATObtainWrapper: The NIZK proof did not verify." << endl;
    }
    niat_token token;
    if (NIATClientVerify(pkI, psig) == true)
    {
        token = NIATObtain(pkI, psig);
    }
    else
    {
        std::cerr << "NIATObtainWrapper: The pre-token's signature failed eq_verification." << endl;
    }
    return token;
}

void NIATIssuer::NIATIssuerKeyGen()
{
    for (int i = 0; i < EQ_SIZE; i++)
    {
        this->skI.x[i].setByCSPRNG();
        this->pkI.X[i] = P * skI.x[i];

        this->skI.y[i].setByCSPRNG();
        this->pkI.Y[i] = Q * skI.y[i];
    }
}

niat_psig NIATIssuer::NIATIssue(const pkC_t &pkC, const int b)
{
    std::string r = "randomness r is hardcoded for this proof of concept";
    G1 R;
    HashtoG1(R, r);
    G1 S = R * this->skI.x[b]; // use corresponding sk depends on the bit b

    eq_msg m = {pkC, (R + S)};
    niat_psig ret = {
        .sig = EQSign(this->skI.y, m),
        .S = S,
        .nonce = r,
        .pi = NIZKProve(R, S, b),
    };
    return ret;
}

/*
 * wrapper for EQVerify on the issuer side, using the precomputed e
 */
bool NIATIssuer::NIATIssuerVerify(niat_token &token)
{
    eq_msg m = {P, (token.tag[0] + token.tag[1])};
    return EQVerify(pkI.Y, m, token.sig, this->eI);
}

int NIATIssuer::NIATReadBit(niat_token &token)
{
    int b = -1;
    // Token verification can be run independently of ReadBit, ideally in parallel,
    // so won't be included here
    if ((token.tag[0] * this->skI.x[0]) == token.tag[1])
    {
        b = 0;
    }
    else if ((token.tag[0] * this->skI.x[1]) == token.tag[1])
    {
        b = 1;
    }
    else
    {
        std::cerr << "NIATReadBit: Error while extracting bit." << endl;
    }
    return b;
}


/* public (but slower) NIAT token verification.
 * client and issuer can do this slightly faster.
 */
inline bool NIATPublicVerify(pkI_t &pkI, niat_token &token)
{
    eq_msg m = {P, (token.tag[0] + token.tag[1])};
    // note that messages at different stages are different!
    return EQVerify(pkI.Y, m, token.sig);
}


/* ------------------------------ tests ------------------------------ */

void test_EQ_signatures()
{
    Debug("\n------------------------- EQ tests --------------------------\n");
    eq_sk skEQ;
    eq_pk pkEQ;
    EQKeyGen(skEQ, pkEQ);

    eq_msg message;
    for (int i = 0; i < EQ_SIZE; i++)
    {
        Fr rand;
        rand.setByCSPRNG();
        message[i] = P * rand;
    }
    eq_sig signature = EQSign(skEQ, message);
    bool before = EQVerify(pkEQ, message, signature);
    Fr mu;
    mu.setByCSPRNG();
    eq_sig newSignature = EQChRep(signature, mu);
    eq_msg newMessage = EQAdaptMessage(message, mu);
    bool after = EQVerify(pkEQ, newMessage, newSignature);
    Debug("SPS-EQ algorithms: \t" << (before == after ? "ok" : "failed") << endl);
}

void test_NIAT_tokens()
{
    Debug("\n------------------------- NIAT tests ------------------------\n");
    NIATIssuer issuer;
    issuer.NIATIssuerKeyGen();
    issuer.precompute();
    NIATClient client;
    client.NIATClientKeyGen();
    client.precompute(issuer.pkI);

    for (int b = 0; b < 2; b++)
    {
        Debug("\n------------------------- b=" << b << " -------------------------------\n");
        // issue
        niat_psig pretoken = issuer.NIATIssue(client.pkC, b);
        
        Debug("Client obtains.." << endl);
        // client does the following to obtain
        niat_token token;
        {
            // client
            G1 R;
            HashtoG1(R, pretoken.nonce);
            bool nizkOk = client.NIZKVerify(issuer.pkI, R, pretoken.S, pretoken.pi);
            bool eqOk = client.NIATClientVerify(issuer.pkI, pretoken);
            if (nizkOk && eqOk)
            {
                token = client.NIATObtain(issuer.pkI, pretoken);
            }
        }
        // all of the steps are wrapped in
        // niat_token token = client.NIATObtainWrapper(issuer.pkI, pretoken);
        
        Debug("Client redeems.." << endl);

        bool tokenOk = issuer.NIATIssuerVerify(token);
        Debug("Token valid? \t" << (tokenOk?"ok":"invalid") << endl);

        int b_ = issuer.NIATReadBit(token);
        if (b_ == -1)
        {
            std::cerr << "Big error in NIAT protocol!" << endl;
        }
        else
        {
            Debug("ReadBit expects " << b << "\t" << ((b == b_) ? "ok" : "failed") << endl);
        }
    }
}

void test_NIAT_Issuer_batching()
{
    Debug("\n------------------ NIAT with batching tests -----------------\n");
    NIATIssuer issuer;
    issuer.NIATIssuerKeyGen();
    issuer.precompute();
    NIATClient client;
    client.NIATClientKeyGen();
    client.precompute(issuer.pkI);

    int numTokens = 100;
    vector<niat_psig> preTokenBatch;

    // issue a batch of pre-tokens
    for (int i = 0; i < numTokens; i++) {
        int b = i % 2;
        niat_psig pretoken = issuer.NIATIssue(client.pkC, b);
        preTokenBatch.push_back(pretoken);
    }

    // client obtains a batch
    vector<niat_token> tokenBatch;
    bool nizkAllOk = true;
    { 
        Debug("Client" << endl);
        // verify NIZK one by one
        for (int i = 0; i < numTokens; i++) {
            G1 R;
            HashtoG1(R, preTokenBatch[i].nonce);
            bool nizkOk = client.NIZKVerify(issuer.pkI, R, preTokenBatch[i].S, preTokenBatch[i].pi);
            nizkAllOk = nizkAllOk & nizkOk;
        }
        Debug("Pretokens NIZK verified: \t" << (nizkAllOk ? "ok" : "failed") << endl);
        
        // batch eq verify
        bool eqAllOk = client.NIATClientBatchVerify(issuer.pkI, preTokenBatch);
        Debug("Pretoken batch EQ Verified: \t" << (eqAllOk ? "ok" : "failed") << endl);

        // computes final token one by one.
        // This can be run independently of eq_verify?
        if (nizkAllOk && eqAllOk) {
            for (int i = 0; i < numTokens; i++) {
                niat_token tok = client.NIATObtain(issuer.pkI, preTokenBatch[i]);
                tokenBatch.push_back(tok);
            }   
        }
    }
    
    // assume client submits a batch of tokens
    // verifier does
    {
        Debug("Issuer." << endl);
        // one thread runs the eq verify
        bool ok = issuer.NIATIssuerBatchVerify(tokenBatch);
        Debug("Token batch EQ Verified: \t" << (ok ? "ok" : "failed") << endl);

        // one thread extract the bits
        for (int i = 0; i < numTokens; i++) {
            int b_ = issuer.NIATReadBit(tokenBatch[i]);
            if (b_ == -1)
            {
                std::cerr << "Big error in NIAT protocol!" << endl;
            }
            else if (b_ != (i % 2))
            {
                Debug("test_NIAT_Issuer_batching: token[" << i << "] expects b=" << (i % 2) << " but got " << b_ << endl);
            }
        }
        Debug("No error during bit extraction." << endl);
    }
}

/* ------------------------------ main ------------------------------ */

/* setup global parameters */
void setup()
{
    initPairing(mcl::BLS12_381);
    mapToG1(P, 1);
    mapToG2(Q, 1);
}

int main()
{
    setup();
    test_EQ_signatures();
    test_NIAT_tokens();
    test_NIAT_Issuer_batching();

    return 0;
}


/* --------------------------- Optimization  -------------------------------
 * Optimizations specific to the NIAT protocol
 * -------------------------------------------------------------------------*/

void NIATClient::precompute(const pkI_t &pkI)
{
    // e(pkC, pkI^(3)) in paper
    pairing(this->eC, this->pkC, pkI.Y[0]);
}

void NIATIssuer::precompute()
{
    // e(g1, pkI^(3)) in paper
    pairing(this->eI, P, pkI.Y[0]);
}

/** 
 * Overloaded EQVerify taking a precomputed pairing.
 * used by client and issuer.
*/
bool EQVerify(const eq_pk &pk, const eq_msg &m, const eq_sig &s, const GT &ePrecomputed)
{
    if (m.size() != pk.size())
    {
        throw std::runtime_error("EQVerify: Size of message and public key mismatched.");
    }
    // e(g1, Y2) = e(Y1, g2)
    GT e1, e2;
    pairing(e1, P, s.Y2);
    pairing(e2, s.Y1, Q);

    // e(m1, pk1) * e(m2, pk2) = e(Z, Y2)
    // |---l1---|   |---l2---|
    // l1 can be pre-computed by client/issuer
    // and we know EQ_SIZE = 2 elements in the msg/pk arrays
    GT l2, rhs;
    pairing(l2, m[1], pk[1]);
    GT lhs = ePrecomputed * l2;
    pairing(rhs, s.Z, s.Y2);
    return (e1 == e2) && (lhs == rhs);
}

/** 
 * Batched version of EQ Verify
 * 
*/
bool EQBatchVerify(const eq_pk &pk, const vector<eq_msg> &msgs, const vector<eq_sig> &sigs, const GT &ePrecomputed)
{
    if (msgs.size() != sigs.size())
    {
        throw std::runtime_error("EQBatchVerify: Size mismatch between message array and signature array.");
    }
    else if (msgs[0].size() != pk.size())
    {
        throw std::runtime_error("EQBatchVerify: Size mismatch between message and public key.");
    }
    int batchSize = msgs.size(); // n, number of tokens in a batch

    G1 sum_Y1, sum_m1;
    G2 sum_Y2;
    // zero out for sum
    sum_Y1.clear();
    sum_Y2.clear();
    sum_m1.clear();

    std::vector<G1> zArray, m1Array;
    std::vector<G2> y2Array, pk1Array;
    for (int i = 0; i < batchSize; i++)
    {
        sum_Y1 += sigs[i].Y1;
        sum_Y2 += sigs[i].Y2;
        sum_m1 += msgs[i][1];
        zArray.push_back(sigs[i].Z);
        y2Array.push_back(sigs[i].Y2);
    }
    // e(g1, Y2) = e(Y1, g2)
    GT e1, e2;
    pairing(e1, P, sum_Y2);
    pairing(e2, sum_Y1, Q);
    
    // e(m0, pk0) * e(m1, pk1) = e(Z, Y2)
    // |---l1---|   |---l2---|
    GT l1, l2;
    GT::pow(l1, ePrecomputed, batchSize);
    pairing(l2, sum_m1, pk[1]);
    GT lhs = l1 * l2;
    
    GT rhs;
    millerLoopVec(rhs, zArray.data(), y2Array.data(), batchSize);
    finalExp(rhs, rhs);

    return (e1 == e2) && (lhs == rhs);
}

bool NIATIssuer::NIATIssuerBatchVerify(vector<niat_token> &tokens)
{
    vector<eq_msg> msgs;
    vector<eq_sig> sigs;

    for (size_t i = 0; i < tokens.size(); i++)
    {
        eq_msg m = {P, (tokens[i].tag[0] + tokens[i].tag[1])};
        msgs.push_back(m);
        sigs.push_back(tokens[i].sig);
    }
    return EQBatchVerify(this->pkI.Y, msgs, sigs, this->eI);
}

bool NIATClient::NIATClientBatchVerify(const pkI_t &pkI, vector<niat_psig> &psigs)
{
    vector<eq_msg> msgs;
    vector<eq_sig> sigs;

    for (size_t i = 0; i < psigs.size(); i++)
    {
        G1 R;
        HashtoG1(R, psigs[i].nonce);
        eq_msg m = {pkC, (psigs[i].S + R)};
        msgs.push_back(m);
        sigs.push_back(psigs[i].sig);
    }
    return EQBatchVerify(pkI.Y, msgs, sigs, this->eC);
}
