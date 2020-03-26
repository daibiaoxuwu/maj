#include<cstdio>
#include<cstring>
#include<map>
#include <ctime>
#include <vector>
FILE* fin, *fout, *flog;
inline void maxer(int &x, int y) { if (y > x) x = y; }
inline int min(int a, int b) { return a < b ? a : b; }
inline int max(int a, int b) { return a > b ? a : b; }
const double round_prob[19] = {1.000000, 1.000000, 0.999708, 0.998029, 0.991947, 0.976532, 0.946340, 0.897968, 0.831425, 0.750198, 0.660036, 0.567684, 0.479381, 0.399071, 0.329266, 0.270215, 0.221551, 0.182120, 0.00000};
const long long C[5][5] = {{1}, {1, 1}, {1, 2, 1}, {1, 3, 3, 1}, {1, 4, 6, 4, 1}};
const char* mname[]={" 1m", " 2m", " 3m", " 4m", " 5m", " 6m", " 7m", " 8m", " 9m", " 1p", " 2p", " 3p", " 4p", " 5p", " 6p", " 7p", " 8p", " 9p", " 1s", " 2s", " 3s", " 4s", " 5s", " 6s", " 7s", " 8s", " 9s", "EST", "STH", "WST", "NTH", "BAI", " FA", "ZHO"};
const int f_len3 = 15, MX = 16000,MAX_HU_VALUE = 1,CHILD_NUM = 10;
unsigned long long f[16][2][f_len3][MX];
double fsum[16][3][2][5][f_len3];
int dppath[MX][5];
int dpface[MX][2];
double result[f_len3][16];
double fact[136];
int tot;
void seven(const int *hand_cnts, const int *known_remain_cnt,int p, int nw, int k){

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
                    f[p][nw][j][k] += i * thisvec.first[i] * thisvec.second / penalty;
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


int decide(const int *_hand_cnts, const int *known_remain_cnt, const int *dora, int round) {
    round -= 1;
//    time_t start = clock();
    int hand_cnts[35];
    memcpy(hand_cnts, _hand_cnts, 35 * sizeof(int));
    int remaining_cards = 0;
    for (int i = 0; i < 34; ++i) remaining_cards += known_remain_cnt[i];


    int branch_choice_num = 1;
    for (int s = 0; s < 3; ++s) {

    //dp:initialize
        //unsigned long long fsum[16][2][5][f_len3];

        for (int t = 0; t < f_len3; ++t)
            for (int k = 0; k < tot; ++k)
                f[0][0][t][k] = 0;

        f[0][0][0][2] = 1;

        //   printf("\tinit:%lf ms\n",(double)(clock()-start)*1000/CLOCKS_PER_SEC); start=clock();
        //dp
        for (int i = 1; i <= 9; ++i) {
            int nw = i & 1;
            for (int p = 0; p <= branch_choice_num; ++p) {
                for (int t = 0; t < f_len3; ++t)
                    for (int k = 0; k < MX; ++k)
                        f[p][nw][t][k] = 0;
            }
            for (int p = 0; p <= branch_choice_num; ++p) {
                for (int j = min(remaining_cards, f_len3 - 5); j >= 0; --j) {
                    for (int k = 1; k < tot; ++k) {
                        if ((p == branch_choice_num && hand_cnts[s * 9 + i - 1] > 0) ||
                            f[p][nw ^ 1][j][k] > 0) {
                            for (int t = known_remain_cnt[s * 9 + i - 1]; t >= 0; --t) {
                                if (p < branch_choice_num) {
                                    if (dppath[k][hand_cnts[s * 9 + i - 1] + t] < 0 ||
                                        dppath[k][hand_cnts[s * 9 + i - 1] + t] > tot)
                                        printf("error!");
                                    f[p][nw][j + t][dppath[k][hand_cnts[s * 9 + i - 1] + t]] +=
                                            f[p][nw ^ 1][j][k] * C[known_remain_cnt[s * 9 + i - 1]][t];
                                }
                                if (p == branch_choice_num) {
                                    f[p][nw][j + t][dppath[k][hand_cnts[s * 9 + i - 1] - 1 + t]] +=
                                            f[0][nw ^ 1][j][k] * C[known_remain_cnt[s * 9 + i - 1]][t];
                                }
                            }
                        }
                    }
                }
            }
            if (hand_cnts[s * 9 + i - 1] > 0) {
//                for (int s0 = 0; s0 < s; ++s0)
//                    for (int t = 0; t < f_len3 - 5; ++t)
//                        for (int k = 0; k < 5; ++k)
//                            for (int i = 0; i < 2; ++i)
//                                fsum[branch_choice_num][s0][i][k][t] = fsum[0][s0][i][k][t];
                ++branch_choice_num;
            }
        }
        int nw = 9 & 1;   
        for (int p = 0; p <= branch_choice_num; ++p) {
            for (int t = 0; t < f_len3 - 5; ++t)
                for (int k = 0; k < MX; ++k)
                    for (int i = 0; i < 2; ++i)
                        fsum[p][s][i][dpface[k][i]][t] += (double)f[p][nw][t][k];

        }
    }
    /*
    for (int s = 0; s < 3; ++s)
        for (int i1 = 0; i1 < 2; ++i1)
            for (int j1 = 0; j1 < 3; ++j1)
                for (int i = 0; i < f_len3 - 5; ++i)
                    if (fsum[1][s][i1][j1][i] > 0) {
                        printf("%d %d %d\n", s, i1, j1);
                        break;
                    }*/
    int p = 1;
    for (int n = 0; n < 34; ++n) {
        if(hand_cnts[n] == 0)continue;
        int m[3], t[3];
        for (m[0] = 0; m[0] <= 4; ++m[0]) {
            for (t[0] = 0; t[0] < f_len3 - 5; ++t[0]) {
                for (m[1] = 0; m[1] <= 4; ++m[1]) {
                    for (t[1] = 0; t[1] + t[0] < f_len3 - 5; ++t[1]) {
                        for (m[2] = max(0, 4 - m[0] - m[1]); m[2] <= 4; ++m[2]) {
                            for (t[2] = 0; t[2] + t[1] + t[0] < f_len3 - 5; ++t[2]) {
                                for (int qt = 0; qt < 3; ++qt) {
                                    double res = 1;
                                    for (int s = 0; s < 3; ++s) {
                                        res *= fsum[(n/9==s?p:0)][s][s == qt ? 1 : 0][m[s]][t[s]];
                                    }
                                    result[t[0] + t[1] + t[2]][p] += res;
                                }
                            }
                        }
                    }
                }
            }
        }
        ++p;
    }
    p = 1;
    double bestval = 0; int bestc = -1;
    for (int l = 0; l < 34; ++l) {
        if(hand_cnts[l]==0)continue;
        double val = 0;
        for (int t = 1; t <= f_len3 - 5; ++t) {
            double prob =
                    (round_prob[min(t - 1 + round, 18)] - round_prob[min(t + round, 18)]) / round_prob[min(round, 18)];
            val += result[t - 1][p] * prob;
        }
//        printf("%s %lf\n",mname[l],val);
        if(val>bestval)bestval=val,bestc=l;
        p++;
    }
//    printf("\tcalc:%lf ms\n",(double)(clock()-start)*1000/CLOCKS_PER_SEC); start=clock();
    return bestc;
    /*
    for (int p = 1; p < branch_choice_num; ++p) {
        int nw = 34 & 1;
        hand_cnts[hand_choices[p - 1]]--;
        seven(hand_cnts, known_remain_cnt, p, nw, 2);
        hand_cnts[hand_choices[p - 1]]++;
    }
     */
   // printf("\tseven:%lf ms\n",(double)(clock()-start)*1000/CLOCKS_PER_SEC); start=clock();
    //dp over
/*
    //expectance
    double expectance[43] = {}, success[43] = {};
    int close_to_hu[43] = {};
    int close_to_hu_min = 100;
    int p = 1;
    for (int card = 0; card < 34; ++card) {

        if(hand_cnts[card] == 0) continue;

        for (int i = 1; i <= f_len3 - 5; ++i) {
            //dora penalty
            int dora_count = 0, dora_penalty = 0;
            for (int j = 0; j < 34; ++j) { dora_count += dora[i]; }
            if (dora[card] >= hand_cnts[card]) dora_penalty = 1;
            if (card >= 27 && hand_cnts[card] <= 1) dora_penalty = 0;//don't save
            dora_penalty = 0;

            //possibility of lasting to this round
            double prob =
                    (round_prob[min(i - 1 + round, 18)] - round_prob[min(i + round, 18)]) / round_prob[min(round, 18)];

            //expectance
            unsigned long long sum = 0, sum2 = 0;

            for (int j = 1; j <= MAX_HU_VALUE; ++j) {
                sum += f[p][nw][i][j] *
                       (j * 2 + 4 + (dora_count - dora_penalty) * 1);//dora value?//compensate for loss of seven
                sum2 += f[p][nw][i][j];
            }

            if (sum > 0 && close_to_hu[card] == 0) close_to_hu[card] = i;
            if (sum > 0) close_to_hu_min = min(close_to_hu_min, i);
            expectance[p] += (sum * fact[i] * fact[remaining_cards - i] / fact[remaining_cards]) * prob;
            success[p] += (sum2 * fact[i] * fact[remaining_cards - i] / fact[remaining_cards]) * prob;
        }
        p++;
    }



    //best expectance
    int real_best_card = 0;

    double max_exp = -100, suc = 0;
    int best_card = 0;
    int max_card_cnt = 0;
    int maxp = 0;
    for (int l = 1; l < branch_choice_num; ++l) {
        max_exp = -100;
        suc = 0;
        best_card = 0;
        max_card_cnt = 0;
        maxp = 0;
        for (int p = 1; p < branch_choice_num; ++p) {
            int card = hand_choices[p - 1];
            int card_cnt = 4 - (known_remain_cnt[card] + hand_cnts[card]);//cards on table
            if (expectance[p] > max_exp)
                max_exp = expectance[p], best_card = card, suc = success[p], max_card_cnt = card_cnt, maxp = p;
        }

        for (int p = 1; p < branch_choice_num; ++p) {
            int card = hand_choices[p - 1];
            int card_cnt = 4 - (known_remain_cnt[card] + hand_cnts[card]);//cards on table
            if (expectance[p] >= max_exp - 0.005 && card_cnt > max_card_cnt) {
                printf("%3s %lf %d safer than %3s %lf %d\n", mname[card], expectance[p], card_cnt, mname[best_card],
                       max_exp, max_card_cnt);
                max_exp = expectance[p] + 0.005, best_card = card, suc = success[p], max_card_cnt = card_cnt, maxp = p;
            }
        }
        //max ting
        unsigned long long ting_card_cnt = 0;
        for (int j = 1; j <= MAX_HU_VALUE; ++j) {
            ting_card_cnt += f[maxp][34 & 1][1][j];
        }

        if (close_to_hu[best_card] == 1) {
            for (int p = 1; p <= branch_choice_num; ++p) {
                int card = hand_choices[p - 1];
                unsigned long long sum = 0;
                for (int j = 1; j <= MAX_HU_VALUE; ++j) {
                    sum += f[p][34 & 1][1][j];
                }
                if (sum > ting_card_cnt) ting_card_cnt = sum, best_card = card;
            }
        }
        printf("%lf %lf %d ", max_exp, suc, close_to_hu[best_card]);
        printf("%3s\n", mname[best_card]);
        expectance[maxp] = 0;
        success[maxp] = 0;
        if(l==1) real_best_card = best_card;
    }
    //safe
    */
    /*
    if(round >= 8 && suc < 0.01){
        printf("safe: ");
        int min_cnt = 5, hand_cnt = 0;
        for (int p = 1; p < branch_choice_num; ++p) {
            int card = hand_choices[p - 1];
            int cnt = hand_cnts[card] + known_remain_cnt[card];
            if (card >= 27 && cnt != 4) cnt -= 1;
            if(cnt < min_cnt || (cnt == min_cnt && hand_cnts[card] >= hand_cnt)) min_cnt = cnt, real_best_card = card, hand_cnt = hand_cnts[card];
        }
    }*/

}
int main() {
    clock_t start = clock();

    fact[0] = 1;
    for (int i = 1; i <= 136; ++i) fact[i] = fact[i - 1] * i;

    FILE* fdp = fopen("..\\automation9.txt", "r");
    fscanf(fdp,"%d",&tot);
    for(int i = 1; i <= tot; ++i){
        for (int ci = 0; ci < 5; ++ci) {
            fscanf(fdp, "%d", &dppath[i][ci]);
            fscanf(fdp, "%d", &dpface[i][0]);
            fscanf(fdp, "%d", &dpface[i][1]);
            dpface[i][0] -= (dpface[i][0] == 0 ? 0 : 1);
            dpface[i][1] -= (dpface[i][1] == 0 ? 0 : 1);
        }
    }
    fclose(fdp);

    fin = fopen("input.txt", "r");
    fout = fopen("output.txt", "w");

    time_t rawtime;
    struct tm * timeinfo;
    time ( &rawtime );
    timeinfo = localtime ( &rawtime );

    int rest_num; fscanf(fin,"%d", &rest_num);
    int hand_cnt[35]; for (int i = 0; i < 34; ++ i) fscanf(fin, "%d", &hand_cnt[i]); hand_cnt[34]=0;
    int known_remain_cnt[34]; for (int i = 0; i < 34; ++ i) fscanf(fin,"%d", &known_remain_cnt[i]);
    int dora[34]; for (int i = 0; i < 34; ++ i) fscanf(fin,"%d", &dora[i]);
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
    int choice = decide(hand_cnt, known_remain_cnt,dora,round);
    fprintf(fout,"%d",choice);
    printf("%s",mname[choice]);

    return choice;
}
