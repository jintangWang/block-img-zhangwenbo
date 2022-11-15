#include <stdio.h>
#include <iostream>
#include <string>
#include <cstring>
#include <stdlib.h>
#include "hashlibpp.h"
using namespace std;
const int LEN = 15;
struct Node {
	string s;
	int left, right;
	Node(string _s, int _left, int _right)
		:s(_s), left(_left), right(_right) {
	}
};
Node tree[2010];

string get_hash(string s)
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

int main()
{
	int m;
	cin >> m;
	for (int i = 0; i < m; i++) {
		FILE* fp;
		char str[LEN]
			fp = fopen("./signs/.txt", "r");
		fscanf(fp, "%s", str);
		tree[i] = Node(get_hash(str), -1, -1);
		fclose(fp);
	}

	int l = 0, u = m, k = m;
	while (u - l > 1) {
		for (int i = l; i < u - 1; i += 2) {
			string str = tree[i].s;
			str.append(tree[i + 1].s);
			tree[k++] = Node(get_hash(str), i, i + 1);
		}
		l = u;
		u = k;
	}
	cout << tree[k].s << endl;
	return 0;
}