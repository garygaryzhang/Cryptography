//
//  main.cpp
//  Cryptography
//
//  Created by Gary on 7/6/16.
//  Copyright © 2016 Gary. All rights reserved.
//

#include <iostream>
#include <string>
#include <math.h>
#include <vector>
#include <stack>
#include <queue>

typedef unsigned long ul;
ul mod(ul g, ul k, ul p);

ul mod_of_sub(ul s1, ul s2, ul p){
    s1 = s1 % p;
    s2 = s2 % p;
    s1 = p - s1;
    if(s2 > s1) return s2 - s1;
    else return p - s1 + s2;
}

ul mod_of_sqr(ul g, ul p){
    if (g == 0) return 0;
    ul m = sqrtl(UINT64_MAX);
    ul a = g / m, b = g % m;
    ul aa = a * a, temp = m * m, result = 0;
    for (ul i = 0; i < aa; i++) {
        result = mod_of_sub(result, temp, p);
    }
    result = mod_of_sub(result, b * b, p);
    temp = (a * m) % p;
    for (ul i = 0; i < 2 * b; i++) {
        result = mod_of_sub(result, temp, p);
    }
    return result;
}

ul mod_of_mul(ul s1, ul s2, ul p){
    ul v1, v2, v;
    ul t1 = (s1 < s2)?s1:s2;
    ul t2 = (s1 >= s2)?s1:s2;
    v = ((t2 - t1) % 2 != 0)?(t1 - 1):t1;
    v1 = mod_of_sqr(v + ((t2 - v) / 2), p);
    v2 = mod_of_sqr((t2 - v) / 2, p);
    return ((t2 - t1) % 2 != 0)?mod_of_sub((v1 < v2)?(p - v2 + v1):(v1 - v2 + p),
                                           t2, p):((v1 < v2)?(v1 + (p - v2)):(v1 - v2));
}

ul mod(ul g, ul k, ul p){
    if (g == 0) return 0;
    k = k % (p - 1);
    ul m = sqrtl(UINT64_MAX);
    ul mul = 1, temp = 0;
    for (int i = 0; i < 8 * sizeof(ul); i++) {
        temp = (i == 0)?(g % p):((g <= m)?((temp * temp) % p):mod_of_sqr(temp, p));
        if(((k>>i) & 1) == 0) continue;
        if ((UINT64_MAX / temp) >= mul) mul = (temp * mul) % p;
        else mul = mod_of_mul(temp, mul, p);
    }
    return mul;
}

ul Linear_Equation(ul a, ul b, ul c, ul p){
    std::stack<ul> * stac = new std::stack<ul>();
    b = b % p;
    ul coefficient = mod_of_sub(c, p - b, p), inverse, max, steps = 0, original_p
    = p;
    while (a > 1) {
        stac->push(p / a);
        b = a;
        a = p % a;
        p = b;
        steps++; }
    p = 0; a = 1; max = steps;
    while (steps > 0) {
        b = a;
        a = p + (stac->top() * a);
        stac->pop();
        p = b;
        steps--;
    }
    delete stac;
    inverse = (max % 2 == 0)?a:(original_p - a);
    if ((UINT64_MAX / coefficient) >= inverse) return (coefficient * inverse) %
        original_p;
    return mod_of_mul(coefficient, inverse, original_p);
}

ul ECC_E(long a, long b, long p, ul g1, ul g2, ul k, ul * pointer1, ul * pointer2
         ){
    if (4 * a * a * a + (27 * b * b) == 0) throw -1;
    std::vector<ul> * result_x = new std::vector<ul>();
    std::vector<ul> * result_y = new std::vector<ul>();
    if (mod_of_sqr(g2, p) != mod_of_sub(mod(g1, 3, p), mod_of_sub((a >= 0)?mod_of_mul(a, g1, p):(p - mod_of_mul(-a, g1, p)), b, p), p)) throw -1;
    
    result_x->push_back(g1);
    result_y->push_back(g2);
    ul AB;
    int i = 1;
    do
    {
        i++;
        ul xp, yp, xq, yq, xr, yr;
        ul temp1, temp2;
        if ((i / 2) == (i - (i / 2))){
            xp = (*result_x)[i / 2 - 1];
            yp = (*result_y)[i / 2 - 1];
            if (yp == 0) break;
            AB = mod_of_mul(mod_of_sub(mod_of_mul(3, mod_of_sqr(xp, p), p), (a >=
                                                                             0)?(a % p):(p - ((-a) % p)), p), Linear_Equation
                            (mod_of_mul(2, yp, p), 0, 1, p), p);
            temp1 = mod_of_sqr(AB, p);
            temp2 = mod_of_mul(2, xp, p);
            xr = (temp1 >= temp2)?((temp1 - temp2) % p):(p - ((temp2 - temp1) % p
                                                              ));
            result_x->push_back(xr);
            temp1 = mod_of_mul(AB, (xp >= xr)?((xp - xr) % p):(p - ((xr - xp) % p
                                                                    )), p);
            temp2 = yp % p;
            yr = (temp1 >= temp2)?((temp1 - temp2) % p):(p - ((temp2 - temp1) % p
                                                              ));
            result_y->push_back(yr);
        }
        else{
            xp = (*result_x)[i / 2 - 1];
            yp = (*result_y)[i / 2 - 1];
            xq = (*result_x)[i - (i / 2) - 1];
            yq = (*result_y)[i - (i / 2) - 1];
            if (xp == xq) break;
            AB = mod_of_mul((((xp > xq) && (yp > yq)) || ((xp < xq) && (yp < yq)))?(((yp > yq)?(yp - yq):(yq - yp)) % p):(p - (((yp > yq)?(yp - yq):(yq - yp)) % p)), Linear_Equation((xp > xq)?(xp - xq):(xq - xp), 0, 1, p), p);
            
            temp1 = mod_of_sqr(AB, p);
            temp2 = mod_of_sub(xp, xq, p);
            
            xr = (temp1 >= temp2)?((temp1 - temp2) % p):(p - ((temp2 - temp1) % p));
            
            result_x->push_back(xr);
            
            temp1 = mod_of_mul(AB, (xp >= xr)?((xp - xr) % p):(p - ((xr - xp) % p)), p);
            
            temp2 = yp % p;
            
            yr = (temp1 >= temp2)?((temp1 - temp2) % p):(p - ((temp2 - temp1) % p));
            
            result_y->push_back(yr);
        }
    }
    while(true);
    
    if ((k <= 0) || (k >= i)) {
        for (i = 0; i < result_x->size(); i++) {
            std::cout<<"P"<<i + 1<<" = ("<<(*result_x)[i]<<", "<<(*result_y)[i]<<")"<<std::endl;
        }
        std::cout<<"----------------"<<std::endl<<"Order("<<g1<<", "<<g2<<") = "<<i + 1<<std::endl;
    }
    
    else{
        *pointer1 = (*result_x)[k - 1];
        *pointer2 = (*result_y)[k - 1];
    }
    delete result_x;
    delete result_y;
    return i;
}
ul ECC_E(long a, long b, long p, ul g1, ul g2){
    return ECC_E(a, b, p, g1, g2, 0, NULL, NULL);
}

void ECC_E(long a, long b, long p){
    if (4 * a * a * a + (27 * b * b) == 0) throw -1;
    ul p1, p2, temp1 = 0, temp2, t;
    for (p1 = 0, p2 = 0; p1 < p; p1++)
    {
        temp2 = mod_of_sub(mod(p1, 3, p), mod_of_sub((a >= 0)?mod_of_mul(a, p1, p):(p - mod_of_mul(-a, p1, p)), b, p), p);
        
        t = 0;
        for (p2 = (ul)floorl(sqrtl((long double)temp2)); p2 < p; p2 = (ul)floorl
             (sqrtl((long double)(temp2 + (++t * p))))) {
            if (mod_of_sqr(p2, p) == temp2) {
                std::cout<<"P"<<++temp1<<" = ("<<p1<<", "<<p2<<")"<<std::endl;
                std::cout<<"P"<<++temp1<<" = ("<<p1<<", [X])"<<std::endl;
                break;
            }
        }
    }
    std::cout<<"----------------"<<std::endl<<"N = "<<temp1<<std::endl;
}

void ECC_E_Encryption(ul a, ul b, ul p, ul g1, ul g2, ul k, ul g1_pub, ul g2_pub,
                      ul m1, ul m2){
    if (4 * a * a * a + (27 * b * b) == 0) throw -1;
    if (k >= p) throw -1;
    ul v1, v2, v3, v4;
    ECC_E(a, b, p, g1, g2, k, &v1, &v2);
    ECC_E(a, b, p, g1_pub, g2_pub, k, &v3, &v4);
    std::cout<<"Cipher text = ";
    std::cout<<"{("<<v1<<", "<<v2<<"); "<<mod_of_mul(v3, m1, p)<<"; "<<mod_of_mul(v4, m2, p)<<"}";
}

void ECC_Decryption(ul a, ul b, ul p, ul g1, ul g2, ul k, ul g1_pub, ul g2_pub, ul cipher_m1, ul cipher_m2){
    if (4 * a * a * a + (27 * b * b) == 0) throw -1;
    if (k >= p) throw -1;
    ul v1, v2, v3, v4;
    ECC_E(a, b, p, g1_pub, g2_pub, k,  &v1, &v2);
    v3 = mod_of_mul(cipher_m1, Linear_Equation(v1, 0, 1, p), p);
    v4 = mod_of_mul(cipher_m2, Linear_Equation(v2, 0, 1, p), p);
    std::cout<<"Original text = ";
    std::cout<<"("<<v3<<", "<<v4<<")";
}

ul Zero_Knowledge_TA(ul pq, ul priva){
    if (pq % 4 != 1) throw -1;
    return Linear_Equation(priva * priva, 0, 1, pq);
}

void Zero_Knowledge_Alice(ul pq, ul priva1, ul priva2){
    if (pq % 4 != 1) throw -1;
    if ((pq % priva1 == 0) || (pq % priva2 == 0)) throw -1;
    ul pub1 = Zero_Knowledge_TA(pq, priva1), pub2 = Zero_Knowledge_TA(pq, priva2);
    
    std::cout<<"Alice's public key is ("<<pub1<<", "<<pub2<<")"<<std::endl;
    ul v1 = random() % pq, v2 = rand() % pq, v3 = rand() % pq;
    ul v4 = 0, v5 = 0, v6 = 0;
    int matrix[3][2];
    std::cout<<"Alice sends {"<<mod_of_sqr(v1, pq)<<", "<<mod_of_sqr(v2, pq)<<", "<<mod_of_sqr(v3, pq)<<"} to Bob."<<std::endl;
    std::cout<<"Alice needs to know the matrix from Bob: ";
    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < 2; j++) {
            std::cin>>matrix[i][j];
        }
    }
    v4 = mod_of_mul(v1, mod_of_mul(((matrix[0][0] == 0)?1:priva1), ((matrix[0][1] == 0)?1:priva2), pq), pq);
    v5 = mod_of_mul(v2, mod_of_mul(((matrix[1][0] == 0)?1:priva1), ((matrix[1][1] == 0)?1:priva2), pq), pq);
    v6 = mod_of_mul(v3, mod_of_mul(((matrix[2][0] == 0)?1:priva1), ((matrix[2][1] == 0)?1:priva2), pq), pq);
    std::cout<<"Alice then sends {"<<v4<<", "<<v5<<", "<<v6<<"} to Bob."<<std::endl;
}

void Zero_Knowledge_Bob(ul pq, ul v4, ul v5, ul v6, ul pub1, ul pub2, ul v1, ul v2, ul v3, std::string matrix_msg){
    if (pq % 4 != 1) throw -1;
    std::cout<<"Alice's public key is ("<<pub1<<", "<<pub2<<")"<<std::endl;
    int matrix[3][2];
    sscanf(&(matrix_msg[0]), "%i %i %i %i %i %i", &(matrix[0][0]), &(matrix[0][1]), &(matrix[1][0]), &(matrix[1][1]), &(matrix[2][0]), &(matrix[2][1]));
    
    ul vv1 = 0, vv2 = 0, vv3 = 0;
    
    vv1 = mod_of_mul(mod_of_sqr(v4, pq), mod_of_mul(((matrix[0][0] == 0)?1:pub1),((matrix[0][1] == 0)?1:pub2), pq), pq);
    
    vv2 = mod_of_mul(mod_of_sqr(v5, pq), mod_of_mul(((matrix[1][0] == 0)?1:pub1),((matrix[1][1] == 0)?1:pub2), pq), pq);
    
    vv3 = mod_of_mul(mod_of_sqr(v6, pq), mod_of_mul(((matrix[2][0] == 0)?1:pub1),((matrix[2][1] == 0)?1:pub2), pq), pq);
    
    std::cout<<"Bob's verification is {"<<vv1<<", "<<vv2<<", "<<vv3<<"}"<<std::endl;
    std::cout<<"So, Bob's answer is "<<(((vv1 == v1) && (vv2 == v2) && (vv3 == v3))?"YES.":"NO.")<<std::endl;
}

void Key_sharing_scheme(long a, long b, long c, long n, long m){
    std::vector<long> * vec_x = new std::vector<long>();
    std::vector<long> * vec_y = new std::vector<long>();
    long tem = m + n + 1;
    for (long i = 0; i != ((tem % 2 == 0)?(tem / -2):((tem + 1) / 2)); i = (i > 0)?(-i):(1 - i)) {
        vec_x->push_back(i);
        vec_y->push_back(a * i * i + (b * i) + c);
    }
    std::cout<<"Any President/CEO: ("<<(*vec_x)[1]<<", "<<(*vec_y)[1]<<") & ("<<(*vec_x)[2]<<", "<<(*vec_y)[2]<<") & ("<<(*vec_x)[3]<<", "<<(*vec_y)[3]<<")"<<std::endl;
    
    std::cout<<"Any VP: ("<<(*vec_x)[0]<<", "<<(*vec_y)[0]<<") & one of {";
    
    for (int i = 1; i < m; i++) {
        std::cout<<"("<<(*vec_x)[i]<<", "<<(*vec_y)[i]<<")"<<((i == (m - 1))?"":", ");
    }
    std::cout<<"}"<<std::endl;
    std::cout<<"Any Manager: only one of {";
    for (long i = (m + 1); i < vec_x->size(); i++) {
        std::cout<<"("<<(*vec_x)[i]<<", "<<(*vec_y)[i]<<")"<<((i == (vec_x->size() - 1))?"":", ");
    }
    std::cout<<"}"<<std::endl;
    delete vec_x;
    delete vec_y;
}

void key_sharing_calculation(long p1_x, long p1_y, long p2_x, long p2_y, long p3_x, long p3_y){
    std::cout<<"(a|p); (b|h); (c|d)"<<std::endl;
    std::cout<<"------------------"<<std::endl;
    std::cout<<p1_x * p1_x<<"p + "<<p1_x<<"h + d = "<<p1_y<<std::endl;
    std::cout<<p2_x * p2_x<<"p + "<<p2_x<<"h + d = "<<p2_y<<std::endl;
    std::cout<<p3_x * p3_x<<"p + "<<p3_x<<"h + d = "<<p3_y<<std::endl;
}

int main(int argc, const char * argv[]) {
    ECC_E(1, 6, 11, 2, 4);
    
    //ECC_E(2, 9, 23, 4, 9);
    
    //ECC_E_Encryption(2, 9, 23, 0, 3, 3, 8, 10, 11, 22);
    
    //ECC_Decryption(2, 9, 23, 0, 3, 11, 9, 12, 8, 10);
    
    //Key_sharing_scheme( 1, 2, 5, 3, 4);
    
    
    
}
