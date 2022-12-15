#include <stdio.h>
#include <pbc/pbc.h>
#include <pbc/pbc_field.h>
#include "hashlibpp-master/build/include/hashlibpp.h"
#include <iostream>
#include <stdlib.h>
#include <vector>
#include <set>
#include <time.h>
using namespace std;
const int MAX = 10020, MAX_M = 10100;
int n = 9000;
char id[30], seller[100], buyer[100], times[100], info[400], filename[MAX_M][30];
int m, l, N;
int tmp;
int choosed[MAX_M];
element_t g[MAX];
element_t h, u;
element_t sigma, sigma_i[MAX_M], hash_out[MAX_M];
element_t alpha, sk, beta[MAX], y[MAX], v[MAX_M][MAX];
element_t gama1, gama2;
pairing_t pairing;
pbc_param_t par;

void getParam() {
    FILE* fp;
    fp = fopen("paramVideoFrame.txt", "r");
    // 图片总数量
    fscanf(fp, "%d", &m);
    // 抽检的数量
    fscanf(fp, "%d", &l);
    for (int i = 0; i < m; i++) {
        fscanf(fp, "%s", filename[i]);
    }
    fscanf(fp, "%s", id);
    fscanf(fp, "%s", seller);
    fscanf(fp, "%s", buyer);
    fscanf(fp, "%s", times);
    fclose(fp);
}

//用于将图片处理成向量，输入filename, index，输出vector<int> v
void get_vector(char* filename, int index) {
    signed long int zero = 0, one = 1;

    for (int i = 0; i < N; i++) {
        element_init_Zr(v[index][i], pairing);
    }
    FILE* fp;
    //以二进制方式打开图像
    fp = fopen(filename, "r+");
    if (fp == NULL) {
        perror("File opening failed");
        exit(EXIT_FAILURE);
    }
    int j = 0, size;
    while (!feof(fp) && j < n) {
        int px = fgetc(fp);
        element_set_si(v[index][j++], px);
    }
    size = j;
    while (j < n) {
        element_set(v[index][j], v[index][j % size]);
        j++;
    }
    for (int i = 0; i < m; i++) {
        if (i == index) element_set_si(v[index][j++], one);
        else element_set_si(v[index][j++], zero);
    }
    fclose(fp);
}

//获得哈希值，输出为图片id和图片序号num，输出为指针out
string get_hash(char* s)
{
    hashwrapper* myWrapper = new sha256wrapper();
    string str;
    void* out;
    try {
        str = myWrapper->getHashFromString(s);
    }
    catch (hlException& e) {
        cout << "hash error" << endl;
        exit(0);
    }
    return str;
}

//用于初始化pairing, par(参数param), g[N], sigma, sigma_i[m],
//h, u, gama1, gama2, alpha, sk, beta[l], y[l]
void init()
{
    N = n + m;
    //初始化配对
    pbc_param_init_f_gen(par, 160);
    pairing_init_pbc_param(pairing, par);
    //获取图片向量
    for (int i = 0; i < m; i++) {
        get_vector(filename[i], i);
    }
    //初始化元素
    for (int i = 0; i < N; i++) {//g[N]
        element_init_G1(g[i], pairing);
    }
    element_init_G1(sigma, pairing);//sigma
    for (int i = 0; i < m; i++) { //sigma_i[m]
        element_init_G1(sigma_i[i], pairing);
    }
    element_init_G2(h, pairing);
    element_init_G2(u, pairing);
    element_init_GT(gama1, pairing);
    element_init_GT(gama2, pairing);
    element_init_Zr(alpha, pairing);
    element_init_Zr(sk, pairing);
    for (int i = 0; i < l; i++) {
        element_init_Zr(beta[i], pairing);
    }
    //初始化哈希串
    for (int i = 0; i < m; i++) {
        element_init_G1(hash_out[i], pairing);
        sprintf(info, "%s%s%s%s%d", id, seller, buyer, times, i);
        string str = get_hash(info);
        int len = str.length();
        char* p = new char[len];
        str.copy(p, len, 0);
        void* out = p;
        element_from_hash(hash_out[i], out, 256);
    }

    //random choose
    set<int> s;
    srand(time(0));
    cout << "Choose following images: " << endl;
    for (int i = 0; i < l; i++) {
        int a = rand() % m;
        while (s.count(a)) {
            a = rand() % m;
        }
        s.insert(a);
        choosed[i] = a;
    }

    //得到beta[l]
    for (int i = 0; i < l; i++) {
        element_init_Zr(beta[i], pairing);
        element_random(beta[i]);
    }
    //得到y[l]
    for (int i = 0; i < N; i++) {
        element_init_Zr(y[i], pairing);
        for (int j = 0; j < l; j++) {
            int choose = choosed[j];
            element_t temp;
            element_init_Zr(temp, pairing);
            element_mul(temp, beta[j], v[choose][i]);
            if (j == 0)
                element_set(y[i], temp);
            else
                element_add(y[i], y[i], temp);
        }
    }
}

void Setup(element_t g0[MAX], element_t h0, element_t u0, element_t sk0, int N)
{
    //1. Generate a bilinear group tuple G = (G1, G2, GT , e, ϕ) such that G1, G2, GT have prime
    // order p > 2^k. Choose generators g1, . . ., gN (random)← G1 \ {1} and h (random)← G2 \ {1}.
    for (int i = 0; i < N; i++) {//g[N]
        element_random(g0[i]);
    }

    element_random(h0); //h

    //2.  Choose α(random) ← Fp, and set u : = h^α.
    element_random(alpha);
    element_pow_zn(u0, h, alpha);

    //4. Output p, the public key PK := (G, H, g1, . . . , gN , h, u) and the private key SK := α.
    element_set(sk0, alpha);
}

//给单独一张图片签名
void Sign(element_t sigma0, element_t sk, char* id, int m, int index)
{
    cout << "sign:" << index << endl;
    //Given a secret key SK = α, an identifier id ∈ {0, 1}^k , an integer m indicating the, dimension of the space
    //being signed, and a vector v ∈ F N p , this algorithm sets n := N − m and outputs the signature σ
    //σ := (H(id, 1)^vn+1*……*H(id, m)^vn+m * g1^v1*……*gn^vn)^α
    element_t  sigma_h, sigma_g, sigma_hg, h_tmp, g_tmp;

    element_init_G1(sigma_h, pairing);
    element_init_G1(sigma_g, pairing);
    element_init_G1(sigma_hg, pairing);
    element_init_G1(h_tmp, pairing);
    element_init_G1(g_tmp, pairing);

    //sigma_h = H(id, 1)^vn+1*……*H(id, m)^vn+m
    for (int i = 0; i < m; i++) {
        element_pow_zn(h_tmp, hash_out[i], v[index][i + n]);
        if (i == 0)
            element_set(sigma_h, h_tmp);
        else {
            element_mul(sigma_h, sigma_h, h_tmp);
        }
    }

    //sigma_g = g1^v1*……*gn^vn
    for (int i = 0; i < n; i++) {
        element_pow_zn(g_tmp, g[i], v[index][i]);
        if (i == 0)
            element_set(sigma_g, g_tmp);
        else
            element_mul(sigma_g, sigma_g, g_tmp);
    }

    //sigma_gh = H(id, 1)^vn+1*……*H(id, m)^vn+m * g1^v1*……*gn^vn
    element_mul(sigma_hg, sigma_h, sigma_g);
    //sigma = (H(id, 1)^vn+1*……*H(id, m)^vn+m * g1^v1*……*gn^vn)^α
    element_pow_zn(sigma0, sigma_hg, sk);

    /*element_printf("sigma_%d = %B\n", index, sigma0);
    cout << endl;*/
}

void Combine(element_t sigma0, element_t g[MAX], element_t h, element_t u, element_t beta[MAX_M], element_t sigma_i[MAX_M])
{
    //Given a public key PK, a file identifier id, and l pairs consisting of a weight βi ∈ Fp and a signature σi , this algorithm outputs σ := σ1^β1*……*σl^βl .
    for (int i = 0; i < l; i++) {
        int choose = choosed[i];
        element_t temp;
        element_init_G1(temp, pairing);
        // 公式 3，temp 是得出的值
        element_pow_zn(temp, sigma_i[choose], beta[i]);
        if (i == 0)
            element_set(sigma0, temp);
        else
            element_mul(sigma0, sigma0, temp);
    }
}

// 保存签名的一些参数，以备后面 Verify 使用
void SaveParam() {
    FILE * fp;

    fp = fopen ("signedParam.txt", "w+");
//    fprintf(fp, "%s", g);
//    fprintf(fp, "%s", h);
//    fprintf(fp, "%s", u);
//    fprintf(fp, "%s", id);
//    fprintf(fp, "%s", m);
//    fprintf(fp, "%s", y);
//    pbc_param_out_str(fp, par);
    for (int i = 0; i < m; i++) {
        element_fprintf(fp, "%B\n", sigma_i[i]);
    }
    element_fprintf(fp, "%B\n", sigma);

//    fprintf(fp, "%s", pairing);
//    fprintf(fp, "%s", seller);
//    fprintf(fp, "%s", buyer);
//    fprintf(fp, "%s", times);

    fclose(fp);
}

int main(int argc, char** argv) {

    //获取数据
    getParam();

    //计时
    clock_t t0, t1, t2, t3, t4, t5, t6, t7;

    t0 = clock();

    //初始化配对
    cout << "init...\n" << endl;
    init();
    for (int i = 0; i < l; i++) {
        cout << choosed[i] << " ";
    }
    t1 = clock();
    printf("init: %lf\n", (double)(t1 - t0) / CLOCKS_PER_SEC);

    //执行Setup操作，初始化元素
    cout << "Setup..." << endl;
    Setup(g, h, u, sk, N);
    t2 = clock();
    printf("setup: %lf\n", (double)(t2 - t1) / CLOCKS_PER_SEC);

    //对每个图片签名
    cout << "Sign..." << endl;
    for (int i = 0; i < m; i++) {
        Sign(sigma_i[i], sk, id, m, i);
    }
    t3 = clock();
    printf("sign: %lf\n", (double)(t3 - t2) / CLOCKS_PER_SEC);

    //组合图片签名
    cout << "Combine..." << endl;
    Combine(sigma, g, h, u, beta, sigma_i);
    t4 = clock();
    printf("combine: %lf\n", (double)(t4 - t3) / CLOCKS_PER_SEC);

    printf("sign total time： %lf\n", (double)(t4 - t0) / CLOCKS_PER_SEC );

    t5 = clock();
    cout << "SaveParam..." << endl;
    SaveParam();
    cout << "SaveParam Finish！" << endl;
    printf("save param time： %lf\n", (double)(t5 - t4) / CLOCKS_PER_SEC );

    return 0;
}
