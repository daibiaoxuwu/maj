#include<cstdio>
#include<cstring>
#include<map>
#include <ctime>
#include <vector>
#include <algorithm>
#include <cassert>

FILE* fin, *fout, *flog;
inline void maxer(int &x, int y) { if (y > x) x = y; }
inline int min(int a, int b) { return a < b ? a : b; }
inline int max(int a, int b) { return a > b ? a : b; }
const double round_prob[19] = {1.000000, 1.000000, 0.999708, 0.998029, 0.991947, 0.976532, 0.946340, 0.897968, 0.831425, 0.750198, 0.660036, 0.567684, 0.479381, 0.399071, 0.329266, 0.270215, 0.221551, 0.182120, 0.00000};
const long long C[5][5] = {{1}, {1, 1}, {1, 2, 1}, {1, 3, 3, 1}, {1, 4, 6, 4, 1}};
const char* mname[]={" 1m", " 2m", " 3m", " 4m", " 5m", " 6m", " 7m", " 8m", " 9m", " 1p", " 2p", " 3p", " 4p", " 5p", " 6p", " 7p", " 8p", " 9p", " 1s", " 2s", " 3s", " 4s", " 5s", " 6s", " 7s", " 8s", " 9s", "EST", "STH", "WST", "NTH", "BAI", " FA", "ZHO"};
const int f_len3 = 15, MX = 1000,MAX_HU_VALUE = 1,CHILD_NUM = 10;
unsigned long long f[2][16][f_len3][MX];
double sevenval[16][f_len3];
double fsum[16][4][2][6][f_len3];
int dppath[2][MX][5];
int dpface[2][MX][2];
double result_norm[f_len3][16];
double fact[136];
int tot[2];
int ting_t = 100;
double bestval = -1;
void seven(const int *hand_cnts, const int *known_remain_cnt,int p, int nw, int k){

    memset(sevenval,0,sizeof(double)*16*f_len3);
    int double_cnt = 0;
    for (int i = 0; i < 34; ++i) {
        if(hand_cnts[i]>=2) double_cnt++;
    }
    int remaining_cards = 0;
    for (int i = 0; i < 34; ++i) remaining_cards += known_remain_cnt[i];
    int hand_remain[5]={}, rest_remain[5]={};
    for (int i = 0; i < 34; ++i) {
        if(hand_cnts[i] == 1 || hand_cnts[i] == 3) {
            hand_remain[known_remain_cnt[i]]++;
        }else if(hand_cnts[i]==4){
            hand_remain[known_remain_cnt[i]]+=2;
        }else{
            rest_remain[known_remain_cnt[i]]++;
        }
    }
    auto* starter = new std::vector<int>();
    for (int j : hand_remain) starter->push_back(j);
    for (int j : rest_remain) starter->push_back(j);
    std::map<std::vector<int>, long long int> Hash[2];
    Hash[1][*starter] = 1;
    long long int penalty = 1;
    for (int j = 1; j <= min(remaining_cards, f_len3 - 5); ++j){
        int nw2 = j & 1;
        Hash[nw2 ^ 1].clear();
        for (const auto thisvec : Hash[nw2]) {
            if(thisvec.second == 0) continue;
            int mink;
            for (mink = 0; mink < 5 && thisvec.first[mink] == 0; ++mink);
            if(mink == 5) continue;
            //add a pair
            for (int i = 1; i < 5; ++i) {
                if(thisvec.first[i] == 0) continue;
                auto *newvec = new std::vector<int>();
                for (int k = 0; k < 10; ++k) newvec->push_back(thisvec.first[k]);
                (*newvec)[i] -= 1;
                (*newvec)[i + 5 - 1] += 1;

                int mink2;
                for (mink2 = 0; mink2 < 5 && (*newvec)[mink2] == 0; ++mink2);
                if(mink2 < 5) {
                    (*newvec)[mink2] -= 1;
                    (*newvec)[mink2 + 5] += 1;
                }

                int sum = 0;
                for (int k = 0; k < 5; ++k) sum += thisvec.first[k];

                if(sum <= 2){
                    sevenval[p][j] += i * thisvec.first[i] * thisvec.second;
                } else {
                    if (Hash[nw2 ^ 1].count(*newvec) == 0)
                        Hash[nw2 ^ 1][*newvec] = i * thisvec.first[i] * thisvec.second;
                    else
                        Hash[nw2 ^ 1][*newvec] += i * thisvec.first[i] * thisvec.second;
                }
            }
            //add better hands
            for (int i = 1; i <= mink; ++i) {
                if(thisvec.first[i + 5] <= 0) continue;
                auto *newvec = new std::vector<int>();
                for (int k = 0; k < 10; ++k) newvec->push_back(thisvec.first[k]);
                (*newvec)[i + 5] -= 1;
                (*newvec)[i + 5 - 1] += 1;
                if(Hash[nw2 ^ 1].count(*newvec) == 0) {
                    Hash[nw2 ^ 1][*newvec] = thisvec.first[i + 5] * i * thisvec.second;
                } else {
                    Hash[nw2 ^ 1][*newvec] += thisvec.first[i + 5] * i * thisvec.second;
                }
            }

            for (int i = mink + 1; i < 5; ++i) {
                if(thisvec.first[i + 5] <= 0) continue;
                auto *newvec = new std::vector<int>();
                for (int r = 0; r < 10; ++r) newvec->push_back(thisvec.first[r]);
                (*newvec)[i + 5] -= 1;
                (*newvec)[i - 1] += 1;
                (*newvec)[mink + 5] += 1;
                (*newvec)[mink] -= 1;

                if(Hash[nw2 ^ 1].count(*newvec) == 0){
                    Hash[nw2 ^ 1][*newvec] = thisvec.first[i + 5] * i * thisvec.second;
                } else {
                    Hash[nw2 ^ 1][*newvec] += thisvec.first[i + 5] * i * thisvec.second;
                }
            }
        }
        penalty *= j;
    }
}


void norm(const int *_hand_cnts, const int *_known_remain_cnt, const int *dora, int round, double result[][16], int maxs, int maxf, int duanflag) {
    int hand_cnts[35], known_remain_cnt[35];
    if(duanflag == 0) {
        memcpy(hand_cnts, _hand_cnts, 35 * sizeof(int));
        memcpy(known_remain_cnt, _known_remain_cnt, 35 * sizeof(int));
    }else{
        memcpy(hand_cnts, _hand_cnts, 35 * sizeof(int));
        hand_cnts[0] = hand_cnts[8] = hand_cnts[9] = hand_cnts[17] = hand_cnts[18] = hand_cnts[26] = 0;
        memset(hand_cnts + 27, 0, 7*sizeof(int));
        memcpy(known_remain_cnt, known_remain_cnt, 35 * sizeof(int));
        known_remain_cnt[0] = known_remain_cnt[8] = known_remain_cnt[9] = known_remain_cnt[17] = known_remain_cnt[18] = known_remain_cnt[26] = 0;
        memset(known_remain_cnt + 27, 0, 7*sizeof(int));
    }
    int remaining_cards = 0;
    for (int i = 0; i < 34; ++i) remaining_cards += known_remain_cnt[i];


    int op = 0;
    for (int s = 0; s < maxs; ++s) {
        int branch_choice_num = 1;
        int dpf = (s == 3 ? 1 : 0);

        //dp:initialize
        memset(f, 0, sizeof(long long int) * 2 * 16 * f_len3 * MX);
        f[0][0][0][2] = 1;

        //dp
        for (int i = 1; i <= (dpf == 0 ? 9 : 7); ++i) {
            int nw = i & 1;

            memset(f[nw], 0, sizeof(long long int) * 16 * f_len3 * MX);
            for (int p = 0; p <= branch_choice_num; ++p) {
                for (int j = min(remaining_cards, f_len3 - 5); j >= 0; --j) {
                    for (int k = 1; k <= tot[dpf]; ++k) {
                        if ((p == branch_choice_num && hand_cnts[s * 9 + i - 1] > 0) ||
                            f[nw ^ 1][p][j][k] > 0) {
                            for (int t = known_remain_cnt[s * 9 + i - 1]; t >= 0; --t) {
                                if (p < branch_choice_num) {
                                    if (dppath[dpf][k][hand_cnts[s * 9 + i - 1] + t] <= 0 ||
                                        dppath[dpf][k][hand_cnts[s * 9 + i - 1] + t] > tot[dpf])
                                        printf("error!");
                                    f[nw][p][j + t][dppath[dpf][k][hand_cnts[s * 9 + i - 1] + t]] +=
                                            f[nw ^ 1][p][j][k] * C[known_remain_cnt[s * 9 + i - 1]][t];
                                }
                                if (p == branch_choice_num) {
                                    f[nw][p][j + t][dppath[dpf][k][hand_cnts[s * 9 + i - 1] - 1 + t]] +=
                                            f[nw ^ 1][0][j][k] * C[known_remain_cnt[s * 9 + i - 1]][t];
                                }
                            }
                        }
                    }
                }
            }
            if (hand_cnts[s * 9 + i - 1] > 0) {
                ++branch_choice_num;
            }
        }
        int nw = 9 & 1;   // 9 & 1 == 7 & 1
        for (int p = 0; p < branch_choice_num; ++p) {
            for (int t = 0; t < f_len3 - 5; ++t)
                for (int k = 1; k <= tot[dpf]; ++k)
                    for (int i = 0; i < 2; ++i)
                        fsum[(p == 0 ? 0 : p + op)][s][i][dpface[dpf][k][i]][t] += (double) f[nw][p][t][k];

        }
        op += (branch_choice_num - 1);
    }
    int p = 1;
    for (int n = 0; n < 34; ++n) {
        if (hand_cnts[n] == 0)continue;
        int m[4], t[4];
        for (m[0] = 0; m[0] <= 4; ++m[0]) {
            for (t[0] = 0; t[0] < f_len3 - 5; ++t[0]) {
                for (m[1] = 0; m[1] <= 4; ++m[1]) {
                    for (t[1] = 0; t[1] + t[0] < f_len3 - 5; ++t[1]) {
                        for (m[2] = 0; m[2] <= 4; ++m[2]) {
                            for (t[2] = 0; t[2] + t[1] + t[0] < f_len3 - 5; ++t[2]) {
                                for (m[3] = max(0, maxf - m[0] - m[1] - m[2]); m[3] <= 4; ++m[3]) {
                                    for (t[3] = 0; t[3] + t[2] + t[1] + t[0] < f_len3 - 5; ++t[3]) {
                                        //one qt
                                        if(maxs >= 1)
                                        for (int qt = 0; qt < maxs; ++qt) {
                                            double res = 1;
                                            for (int s = 0; s < maxs; ++s) {
                                                res *= fsum[(n / 9 == s ? p : 0)][s][s == qt ? 1 : 0][m[s] + 1][t[s]];
                                            }
                                            result[t[0] + t[1] + t[2] + t[3]][p] += res;
                                        }
                                        //minus two qt
                                        if(maxs >= 2)
                                        for (int qt2 = 0; qt2 < maxs - 1; ++qt2) {
                                            for (int qt3 = qt2 + 1; qt3 < maxs; ++qt3) {
                                                double res = 1;
                                                for (int s = 0; s < maxs; ++s)
                                                    res *= fsum[(n / 9 == s ? p : 0)][s][s == qt2 || s == qt3 ? 1 : 0][
                                                            m[s] + 1][t[s]];
                                                result[t[0] + t[1] + t[2] + t[3]][p] -= res;
                                            }
                                        }
                                        //plus three qt
                                        if(maxs >= 3)
                                        for (int qt2 = 0; qt2 < maxs; ++qt2) {
                                            double res = 1;
                                            for (int s = 0; s < maxs; ++s) {
                                                res *= fsum[(n / 9 == s ? p : 0)][s][s == qt2 ? 0 : 1][m[s] + 1][t[s]];
                                            }
                                            result[t[0] + t[1] + t[2] + t[3]][p] += res;
                                        }
                                        //minus four qt
                                        double res = 1;
                                        if(maxs >= 4)
                                        for (int s = 0; s < maxs; ++s) {
                                            res *= fsum[(n / 9 == s ? p : 0)][s][1][m[s] + 1][t[s]];
                                        }
                                        result[t[0] + t[1] + t[2] + t[3]][p] -= res;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        ++p;
    }
}

//state: 0: menqing
//1: no yipai, just duanyao
//2: have yipai
int decide(const int *_hand_cnts, const int *known_remain_cnt, const int *dora, int round, int state, int maxf, const int* yi) {
    printf("r:%d\n",round);

    int hand_cnts[35];
    memcpy(hand_cnts, _hand_cnts, 35 * sizeof(int));
    int remaining_cards = 0;
    for (int i = 0; i < 34; ++i) remaining_cards += known_remain_cnt[i];

    memset(result_norm, 0, sizeof(double)*f_len3*16);
    if(state != 1)
        norm(hand_cnts, known_remain_cnt, dora, round, result_norm, 4, maxf, 0);

    if(state != 2) {
        norm(hand_cnts, known_remain_cnt, dora, round, result_norm, 4, maxf, 1);
    }
    double ting_bval = 0; int ting_card = -1;
    double ting_vals[34];
    int p = 1;
    std::vector<std::pair<double, int>> vals;
    for (int l = 0; l < 34; ++l) {
        printf("l:%d\n",l);
        if(hand_cnts[l]==0)continue;
        double val = 0;
        double prob = 0;
        for (int t = 0; t < f_len3 - 5; ++t) {
            double prob2 = result_norm[t][p] * fact[t] * fact[remaining_cards - t] / fact[remaining_cards];
            if(result_norm[t][p] > 0) ting_t = min(ting_t, t);
            printf("%lf ",prob2);
            val += round_prob[min(t + round, 18)] / round_prob[min(round, 17)] * (prob2 - prob);
            prob = prob2;
        }
        ting_vals[l] = result_norm[1][p];

        //seven
        if(maxf == 4) {
            int nw = 1;
            hand_cnts[l]--;
            seven(hand_cnts, known_remain_cnt, p, nw, 2);
            hand_cnts[l]++;
            double val2 = 0;
            prob = 0;
            for (int t = 0; t < f_len3 - 5; ++t) {
                double prob2 = sevenval[p][t] * fact[remaining_cards - t] / fact[remaining_cards];
                if(sevenval[p][t] > 0) ting_t = min(ting_t, t);
                val2 += 2 * round_prob[min(t + round, 18)] / round_prob[min(round, 17)] *
                        (prob2 - prob);//seven multiply by 2
                prob = prob2;
            }
            printf("%3s %lf %lf\n", mname[l], val, val2);
            val += val2;
            ting_vals[l] += sevenval[p][1];
        }

        //dora
        int dora_count = 0, dora_penalty = 0;
        for (int j = 0; j < 34; ++j) { dora_count += dora[j]; }
        if ((dora[l] >= hand_cnts[l]) && !(l >= 27 && hand_cnts[l] <= 1)) val *= 0.85, ting_vals[l] *= 0.5;
        if(state == 0 && yi[l] > 0) val *= (1+0.1*hand_cnts[l]);
        if(ting_vals[l] > ting_bval) ting_bval = ting_vals[l],ting_card = l;

        vals.emplace_back(std::make_pair(val,l));
        p++;
    }
    std::sort(vals.begin(),vals.end(),std::greater<>());
    if(vals[0].first > 0)
    {
        if(ting_vals[vals[0].second] > 0 && ting_card != -1) return ting_card;
        for (auto i : vals){
            printf("%s %lf\n",mname[i.second],i.first);
        }
        bestval = vals[0].first;
        return vals[0].second;
    } else return -1;
}





int main() {
    clock_t start = clock();

    fact[0] = 1;
    for (int i = 1; i <= 136; ++i) fact[i] = fact[i - 1] * i;

    //now no hu node 1, start from 2, 0 and 1 are useless, start from 1
    FILE* fdp = fopen("automation79.txt", "r");
    for (int k = 0; k < 2; ++k) {
        fscanf(fdp, "%d", &tot[k]);
        for (int i = 1; i <= tot[k]; ++i) {
            for (int ci = 0; ci < 5; ++ci) {
                fscanf(fdp, "%d", &dppath[k][i][ci]);
            }
            fscanf(fdp, "%d", &dpface[k][i][0]);
            fscanf(fdp, "%d", &dpface[k][i][1]);
        }
    }
    fclose(fdp);

    fin = fopen("input.txt", "r");

    time_t rawtime;
    struct tm * timeinfo;
    time ( &rawtime );
    timeinfo = localtime ( &rawtime );

    int rest_num; fscanf(fin,"%d", &rest_num);
    int state; fscanf(fin,"%d", &state);
    int maxf; fscanf(fin,"%d", &maxf);
    int hand_cnt[35]; for (int i = 0; i < 34; ++ i) fscanf(fin, "%d", &hand_cnt[i]); hand_cnt[34]=0;
    int known_remain_cnt[34]; for (int i = 0; i < 34; ++ i) fscanf(fin,"%d", &known_remain_cnt[i]);
    int dora[34]; for (int i = 0; i < 34; ++ i) fscanf(fin,"%d", &dora[i]);
    int yi[34];for (int i = 0; i < 34; ++ i) fscanf(fin,"%d", &yi[i]);
    fclose(fin);

    for (int i = 0; i < 34; ++i) {
        for (int j = 0; j < hand_cnt[i]; ++j) {
            printf("%3s ", mname[i]);
        }
    }
    printf("\n");

//    printf("wall: ");
//    for (int i = 0; i < 34; ++ i){if(known_remain_cnt[i] == 0) printf("%3s ", mname[i]);}
//    printf("\nchance: ");
//    for (int i = 0; i < 34; ++ i){if(known_remain_cnt[i] == 1) printf("%3s ", mname[i]);}
//    printf("\n");

    int round = 18 - rest_num / 4;//start with 69 -> 1.end with 0 - 18.
    int choice = decide(hand_cnt, known_remain_cnt, dora, round, state, maxf, yi);
    if (choice == -1) choice = decide(hand_cnt, known_remain_cnt, dora, round - 1, state, maxf, yi);
    if (choice != -1) printf("state:%d maxf:%d %s %d %lf\n\n",state,maxf, mname[choice],ting_t,bestval);
    fout = fopen("output.txt","w");
    fprintf(fout,"%d %d %lf",choice, ting_t,bestval);
    fclose(fout);
    return choice;
}
