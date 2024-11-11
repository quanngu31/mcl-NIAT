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
using std::vector;
using std::endl;

G1 P;   // generator g1 of G1
G2 Q;   // generator g2 of G2

#define USEDEBUG

#ifdef USEDEBUG
    #define Debug(x) std::cout << x
#else
    #define Debug(x)
#endif

/* ------------------------------ EQ-SPS ------------------------------ */

void EQKeyGen(eq_sk& sk, eq_pk& pk) {
    for (int i = 0; i < EQ_SIZE; i++) {
        sk[i].setByCSPRNG();
        pk[i] = Q * sk[i];
    }
}

eq_sig EQSign(const eq_sk& sk, const eq_msg& m) {
    if (m.size() != sk.size()) {
        throw std::runtime_error("EQSign: Size of message and secret key mismatched.");
    }
    Fr nu, nu_inv;
    nu.setByCSPRNG();
    Fr::inv(nu_inv, nu);
    eq_sig s;
    s.Y1 = P * nu_inv;      // Y1 = g1^(1/r)
    s.Y2 = Q * nu_inv;      // Y2 = g2^(1/r)
    s.Z.clear();        // set 0 for addition
    for (int i = 0; i < EQ_SIZE; i++) {
        s.Z += m[i] * sk[i];
    }
    s.Z = s.Z * nu;         // Z = sum(mi^xi)^nu
    return s;
}

bool EQVerify(const eq_pk& pk, const eq_msg& m, const eq_sig& s) {
    if (m.size() != pk.size()) {
        throw std::runtime_error("EQVerify: Size of message and public key mismatched.");
    }
    // e(g1, Y2) = e(Y1, g2)
    GT e1, e2;
    pairing(e1, P, s.Y2);
    pairing(e2, s.Y1, Q);
    // e(m1, pk1) * e(m2, pk2) = e(Z, Y2)
    GT lhs, rhs;
    millerLoopVecMT(lhs, m.data(), pk.data(), EQ_SIZE); // multi-thread
    finalExp(lhs, lhs); // how finalExp is used internally in the library
    pairing(rhs, s.Z, s.Y2);
    return (e1 == e2) && (lhs == rhs);
}

eq_sig EQChRep(const eq_sig& s, const Fr& mu) {
    eq_sig s_;
    Fr psi, psi_inv;
    psi.setByCSPRNG();
    Fr::inv(psi_inv, psi);
    s_.Y1 = s.Y1 * psi_inv;         // Y1' = Y1^(1/psi)
    s_.Y2 = s.Y2 * psi_inv;         // Y2' = Y2^(1/psi)
    s_.Z  = s.Z  * (psi * mu);      // Z'  = Z^(mu * psi)
    return s_;
}

/* Complement function for EQChRep to adapt a message for a ChRep'd signature */
static eq_msg EQAdaptMessage(const eq_msg& m, const Fr& mu) {
    eq_msg m_;
    for (int i=0; i<EQ_SIZE; i++) {
        m_[i] = m[i] * mu;
    }
    return m_;
}

bool EQBatchedVerify()

/* Overloaded */
bool NIATIssuerEQVer(const G2 pkI[3], vector<vector<G1> > m, vector<eqsig> s, int numTokens) {
    G1 Y1i; G2 Y2i;
    // zero out for sum
    G1::mul(Y1i, P, 0);
    G2::mul(Y2i, Q, 0);
    for (int i=0; i < numTokens; i++) {
        G1::add(Y1i, Y1i, s[i].Y1);
        G2::add(Y2i, Y2i, s[i].Y2);
    }
    Fp12 e1, e2;
    pairing(e1, Y1i, Q);
    pairing(e2, P, Y2i);
    if (e1 != e2) {     // e(g1, Y2) = e(Y1, g2), but aggregated
        return false;   // early termination if fails
    }
    // for issuer
    // m[0] = t.tag[0];
    // m[1] = t.tag[1];

    // e(Z, Y2) = e(g1, pk1) * e(t1, pk2) * e(t2, pk3)

    Fp12 temp;
    // set to one for multiplications
    e1.setOne();    // LHS: e(Z, Y2)
    e2.setOne();    // RHS: e(m1, pk1) * e(m2, pk2) * e(m3, pk3)

    for (int i=0; i < numTokens; i++) {
        pairing(temp, s[i].Z, s[i].Y2); e1 *= temp;

        pairing(temp, m[i][0], pkI[1]); e2 *= temp;
        pairing(temp, m[i][1], pkI[2]); e2 *= temp;
    }
    e2 *= e_g1n_pkI1n; // pre-computed pairing
    return (e1 == e2);
}

/* ------------------------------ NIZK  ------------------------------ */

bool NIATClient::NIZKVerify(pkI_t& pkI, const G1& R, const G1& S, nizkpf pi) {
    // statement
    G1 U[2] = { pkI.X[0], pkI.X[1] };
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
        << "S_tilde[0]: " + S_tilde[0].getStr().substr(0,10) << endl
        << "S_tilde[1]: " + S_tilde[1].getStr().substr(0,10) << endl
        << "U_tilde[0]: " + U_tilde[0].getStr().substr(0,10) << endl
        << "U_tilde[1]: " + U_tilde[1].getStr().substr(0,10) << endl
        << "V_tilde:    " + V_tilde.getStr().substr(0,10) << endl
        << "W_tilde:    " + W_tilde.getStr().substr(0,10) << endl
        << "</nizkproof>";
    Fr c_computed;
    c_computed.setHashOf(transcript.str());
    return (c == c_computed);
}

nizkpf NIATIssuer::NIZKProve(const G1& R, const G1& S, const int b) {
    // statement
    G1 U[2] = { this->pkI.X[0], this->pkI.X[1] };
    G2 V = this->pkI.Y[0], W = this->pkI.Y[1];
    // compute the proof
    Fr z[2], c[2], a[2], zv, zw;
    G1 S_tilde[2], U_tilde[2];
    // sampling
    z[b].setByCSPRNG();
    zv.setByCSPRNG();
    zw.setByCSPRNG();
    c[1-b].setByCSPRNG();
    a[1-b].setByCSPRNG();
    // compute
    S_tilde[b] = R * z[b];
    S_tilde[1-b] = (R * a[1-b]) - (S * c[1-b]);
    U_tilde[b] = P * z[b];
    U_tilde[1-b] = (P * a[1-b]) - (U[1-b] * c[1-b]);
    G2 V_tilde = Q * zv;
    G2 W_tilde = Q * zw;
    // transcript
    std::ostringstream transcript;
    transcript << "<nizkproof> " << endl
        << "S_tilde[0]: " + S_tilde[0].getStr().substr(0,10) << endl
        << "S_tilde[1]: " + S_tilde[1].getStr().substr(0,10) << endl
        << "U_tilde[0]: " + U_tilde[0].getStr().substr(0,10) << endl
        << "U_tilde[1]: " + U_tilde[1].getStr().substr(0,10) << endl
        << "V_tilde:    "    + V_tilde.getStr().substr(0,10) << endl
        << "W_tilde:    "    + W_tilde.getStr().substr(0,10) << endl
        << "</nizkproof>";
    Fr cTotal;
    cTotal.setHashOf(transcript.str());
    // keep computing
    Fr av = zv + (cTotal * this->skI.y[0]);
    Fr aw = zw + (cTotal * this->skI.y[1]);
    c[b] = cTotal - c[1-b];
    a[b] = z[b] + (c[b] * this->skI.x[b]);
    nizkpf pi = {
        .c0 = c[0],
        .c1 = c[1],
        .av = av,
        .aw = aw,
        .a0 = a[0],
        .a1 = a[1]
    };
    return pi;
}

/* ------------------------------ NIAT  ------------------------------ */

void NIATClient::NIATClientKeyGen() {
    this->skC.setByCSPRNG();
    this->pkC = P * skC;
    Fr::inv(this->skC_inverse, this->skC);  // pre-compute the inverse
}

niat_token NIATClient::NIATObtain(pkI_t& pkI, niat_psig& psig, bool eqVerified) {
    G1 R; HashtoG1(R, psig.nonce);
    if ( NIZKVerify(pkI, R, psig.S, psig.pi) != true ) {
        std::cerr << "NIATObtain: The NIZK proof did not verify." << endl;
    }

    niat_token token;
    eq_msg m = { pkC, (psig.S + R) };
    if ( !eqVerified && EQVerify(pkI.Y, m, psig.sig) != true ) {
        std::cerr << "NIATObtain: The pre-token's signature was not verified and failed eq_verification." << endl;
    } else if (EQVerify(pkI.Y, m, psig.sig) != true ) {
        std::cerr << "NIATObtain: The pre-token's signature failed eq_verification." << endl;
    }
    else {
        // everything valid
        eq_msg _tag = { (R * this->skC_inverse), (psig.S * this->skC_inverse) };     // this is not actually a message to any EQ algorithms, but anyway..
        eq_sig _sig = EQChRep(psig.sig, this->skC_inverse);
        token.tag = _tag;
        token.sig = _sig;

        // eq_msg _newmsg = EQAdaptMessage(m, this->skC_inverse);  // we don't need this in the protocol
        // if ( EQVerify(pkI.Y, _newmsg, sig) == true ) {
        // if ( NIATPublicVerify(pkI, token) == true ) {
        //     Debug("--> Immediately after obtain and change rep, EQ Verify is fine" << endl);
        // } else {
        //     Debug("--> Immediately after obtain and change rep, EQ Verify FAILED" << endl);
        // }
    }
    return token;
}


void NIATIssuer::NIATIssuerKeyGen() {
    for (int i=0; i<EQ_SIZE; i++) {
        this->skI.x[i].setByCSPRNG();
        this->pkI.X[i] = P * skI.x[i];

        this->skI.y[i].setByCSPRNG();
        this->pkI.Y[i] = Q * skI.y[i];
    }
}

niat_psig NIATIssuer::NIATIssue(const pkC_t& pkC, const int b) {
    std::string r = "randomness r is hardcoded for this proof of concept";
    G1 R; HashtoG1(R, r);
    G1 S = R * this->skI.x[b];  // use corresponding sk depends on the bit b

    eq_msg m = {pkC, (R + S)};
    niat_psig ret = {
        .sig = EQSign(this->skI.y, m),
        .S = S,
        .nonce = r,
        .pi = NIZKProve(R, S, b),
    };
    // if ( EQVerify(this->pkI.Y, m, ret.sig) == true ) {
    //     Debug("Immediately after issue, EQverify is fine!" << endl);
    // }
    return ret;
}

int NIATIssuer::NIATReadBit(niat_token& token, bool eqVerified) {
    int b = -1;
    if ( !eqVerified && NIATPublicVerify(pkI, token) != true ) {
        std::cerr << "NIATReadBit: Token's signature was not verified and failed verification." << endl;
    } else if ( NIATPublicVerify(pkI, token) != true ) {
        std::cerr << "NIATReadBit: Token's signature failed verification." << endl;
    } else {
        if ( (token.tag[0] * this->skI.x[0]) == token.tag[1] ) {
            b = 0;
        } else if ( (token.tag[0] * this->skI.x[1]) == token.tag[1] ) {
            b = 1;
        } else {
            std::cerr << "NIATReadBit: Error extracting bit." << endl;
        }
    }
    return b;
}

bool NIATPublicVerify(pkI_t& pkI, niat_token& token) {
    eq_msg m = { P, (token.tag[0] + token.tag[1]) };    // note that messages at different stages are different!
    return EQVerify(pkI.Y, m, token.sig);
}

/* ------------------------------ tests ------------------------------ */
void test_EQ_signatures() {
    Debug("\n------------------------- EQ tests ------------------------\n");
    eq_sk skEQ;
    eq_pk pkEQ;
    EQKeyGen(skEQ, pkEQ);

    eq_msg message;
    for (int i=0; i<EQ_SIZE; i++) {
        Fr rand;
        rand.setByCSPRNG();
        message[i] = P * rand;
        // Debug("message [" << i << "] = " << message[i] << endl);
    }
    // Debug("----" << endl);

    eq_sig signature = EQSign(skEQ, message);
    // Debug("EQ Sign" << endl);
    // Debug("Signature Y1 = " << signature.Y1 << endl);
    // Debug("Signature Y2 = " << signature.Y2 << endl);
    // Debug("Signature YZ = " << signature.Z << endl);
    // Debug("----" << endl);

    bool before = EQVerify(pkEQ, message, signature);
    // Debug("EQ Verify, before changeRep " << (before?"ok":"failed") << endl);
    // Debug("----" << endl);

    Fr mu; mu.setByCSPRNG();
    eq_sig newSignature = EQChRep(signature, mu);
    eq_msg newMessage = EQAdaptMessage(message, mu);
    bool after = EQVerify(pkEQ, newMessage, newSignature);
    // Debug("EQ Verify, before changeRep " << (after?"ok":"failed") << endl);
    Debug("SPS-EQ algorithms: \t" << (before==after ? "ok" : "failed") << endl);
}

void test_NIAT_tokens() {
    Debug("\n------------------------- NIAT tests ------------------------\n");
    NIATClient client; client.NIATClientKeyGen();
    NIATIssuer issuer; issuer.NIATIssuerKeyGen();

    for (int b=0; b<2; b++) {
        Debug("\n------------------------- b=" << b << "-------------------------\n");
        niat_psig pretoken = issuer.NIATIssue(client.pkC, b);
        niat_token token   = client.NIATObtain(issuer.pkI, pretoken);

        int b_ = issuer.NIATReadBit(token);
        if (b_ == -1) {
            std::cerr << "Big error in NIAT protocol!" << endl;
        } else {
            Debug("ReadBit: " << b << "\t" << ((b==b_) ? "ok" : "failed") << endl);
        }
    }
}

/* ------------------------------ main ------------------------------ */

/* setup global parameters */
void setup() {
    initPairing(mcl::BLS12_381);
    mapToG1(P, 1);
    mapToG2(Q, 1);
}

int main() {
    setup();
    test_EQ_signatures();
    test_NIAT_tokens();

    return 0;
}
