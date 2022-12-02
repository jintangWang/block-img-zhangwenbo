#include <stdio.h>
#include <pbc/pbc.h>
#include <pbc/pbc_field.h>
#include "hashlibpp-master/build/include/hashlibpp.h"
#include <iostream>
#include <stdlib.h>
#include <vector>
#include <set>
#include <time.h>
#include <typeinfo>
using namespace std;
//const int MAX = 10020, MAX_M = 10100;
const int MAX = 256,MAX_M=10100;
int n = 9000;
char id[30], seller[100], buyer[100], times[100], info[400], filename[MAX_M][30];
int m, l, N;
int tmp;
int choosed[MAX_M];
element_t g[MAX];
element_t h, u;
element_t sigma, sigma2, sigma_i[MAX_M], hash_out[MAX_M];
element_t alpha, sk, beta[MAX], y[MAX], v[MAX_M][MAX];
element_t gama1, gama2;
pairing_t pairing;
pbc_param_t par;

element_t k1, k2;

void getParam()
{
    FILE* fp;
    fp = fopen("param100.txt", "r");
    fscanf(fp, "%d", &m);
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

    element_t x;
    cout<<"开始打印v"<<endl;
    cout<<"打印完成"<<endl;
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
    cout<<"str类型为"<<typeid(str).name()<<endl;
    return str;
}

//用于初始化pairing, par(参数param), g[N]
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
    element_init_G1(k1, pairing);
    element_init_G1(k2, pairing);

    //random choose
    set<int> s;
    srand(time(0));

    clock_t t0, t1, t2, t3, t4, t5, t6, t7;
    t0 = clock();
    cout << "Choose following images: " << l << endl;
    for (int i = 0; i < l; i++) {
        int a = rand() % m;
        while (s.count(a)) {
            a = rand() % m;
        }
        s.insert(a);
        choosed[i] = a;
    }
    t1 = clock();
    printf("ChalGen: %lf\n", (double)(t1 - t0) / CLOCKS_PER_SEC);



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

// 将 element_t 转为 hash
string get_hash_from_element(element_t element_in) {
    unsigned char buffer[180];
    element_to_bytes(buffer, element_in);
    std::string str(reinterpret_cast<char*>(buffer));
    hashwrapper* myWrapper = new sha256wrapper();
    string result = myWrapper->getHashFromString(str);
    return result;
}

// keygen mac算法
void Setup(element_t g0[MAX], element_t h0, element_t u0, element_t sk0, int N)
{
    //1. Generate a bilinear group tuple G = (G1, G2, GT , e, ϕ) such that G1, G2, GT have prime
    // order p > 2^k. Choose generators g1, . . ., gN (random)← G1 \ {1} and h (random)← G2 \ {1}.
    for (int i = 0; i < N; i++) {//g[N]
        element_random(g0[i]);
    }


    //2.  生成 k1、k2 ← Fq
    element_random(k1);
    element_random(k2);

    //3. u ← G(k1)， 用 sha256充当伪随机生成器 G
    string hash_k1 = get_hash_from_element(k1);
    cout << "hash_k1:\n" << hash_k1 << endl;

    //4. b ← F(k2, (id, i))

}

//给单独一张图片签名
void Sign(element_t sigma0, element_t sk, char* id, int m, int index)
{

}

void Combine(element_t sigma0, element_t g[MAX], element_t h, element_t u, element_t beta[MAX_M], element_t sigma_i[MAX_M])
{

}

void Verify(element_t g[MAX], element_t h, element_t u, char* id, int m, element_t y[MAX], element_t sigma_)
{

}


int main(int argc, char** argv) {

    //获取数据
    getParam();
    //inputParam();
    const char*s ="123456";
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
    element_t xx;
    unsigned char *str1=(unsigned char*)str.c_str();
    element_from_bytes(xx,str1);
    //element_printf("转换后为%B",xx);
    //计时
    clock_t t0, t1, t2, t3, t4, t5, t6, t7;

    t0 = clock();

    //初始化配对
    cout << "init..." << endl;
    init();
    for (int i = 0; i < l; i++) {
        cout << choosed[i] << " ";
    }
    cout << endl;
    t1 = clock();
    printf("init: %lf\n", (double)(t1 - t0) / CLOCKS_PER_SEC);

    //执行Setup操作，初始化元素
    cout << "Setup..." << endl;
    Setup(g, h, u, sk, N);
    t2 = clock();
    printf("setup: %lf\n", (double)(t2 - t1) / CLOCKS_PER_SEC);

    //对每个图片签名
//    cout << "Sign..." << endl;
//    for (int i = 0; i < m; i++) {
//        Sign(sigma_i[i], sk, id, m, i);
//    }
//    t3 = clock();
//    printf("sign: %lf\n", (double)(t3 - t2) / CLOCKS_PER_SEC);
//
//    //组合图片签名
//    cout << "Combine..." << endl;
//    Combine(sigma, g, h, u, beta, sigma_i);
//    t4 = clock();
//    printf("combine: %lf\n", (double)(t4 - t3) / CLOCKS_PER_SEC);
//
//    //验证
//    cout << "Verify..." << endl;
//    Verify(g, h, u, id, m, y, sigma);
//    t5 = clock();
//    printf("verify: %lf\n", (double)(t5 - t4) / CLOCKS_PER_SEC);

    //writeSigns();

//    cout << "Verify2" << endl;
//    t6 = clock();
//    for (int i = 0; i < m; i++) {
//        Verify(g, h, u, id, m, v[i], sigma_i[i]);
//    }
    t7 = clock();   
//    printf("verify2: %lf\n", (double)(t7- t6) / CLOCKS_PER_SEC);
    printf("total time： %lf\n", (double)(t7 - t0) / CLOCKS_PER_SEC );
    return 0;
}
