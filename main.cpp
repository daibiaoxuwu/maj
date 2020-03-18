#include<cstdio>
#include<cstring>
#include<map>
#include <ctime>
#include <vector>
#include <cassert>
FILE* fin, *fout, *flog;
inline void maxer(int &x, int y) { if (y > x) x = y; }
inline int min(int a, int b) { return a < b ? a : b; }
inline int max(int a, int b) { return a > b ? a : b; }
const double round_prob[19] = {1.000000, 1.000000, 0.999708, 0.998029, 0.991947, 0.976532, 0.946340, 0.897968, 0.831425, 0.750198, 0.660036, 0.567684, 0.479381, 0.399071, 0.329266, 0.270215, 0.221551, 0.182120, 0.00000};
const long long C[5][5] = {{1}, {1, 1}, {1, 2, 1}, {1, 3, 3, 1}, {1, 4, 6, 4, 1}};
const char* mname[]={" 1W", " 2W", " 3W", " 4W", " 5W", " 6W", " 7W", " 8W", " 9W", " 1B", " 2B", " 3B", " 4B", " 5B", " 6B", " 7B", " 8B", " 9B", " 1T", " 2T", " 3T", " 4T", " 5T", " 6T", " 7T", " 8T", " 9T", "EST", "STH", "WST", "NTH", "BAI", " FA", "ZHO"};
const int f_len3 = 15, MX = 16000,MAX_HU_VALUE = 6,CHILD_NUM = 10;
unsigned long long f[16][2][f_len3][MX];
int dppath[MX][5][CHILD_NUM];
double fact[136];
int tot;
void seven(const int *hand_cnts, const int *known_remain_cnt,int p, int nw, int k){

    int double_cnt = 0;
    for (int i = 0; i < 34; ++i) {
        if(hand_cnts[i]>=2) double_cnt++;
    }
//    if(double_cnt < 4) return;
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
    for (int j = 0; j < 5; ++j) starter->push_back(hand_remain[j]);
    for (int j = 0; j < 5; ++j) starter->push_back(rest_remain[j]);
    std::map<std::vector<int>, long long int> Hash[2];
    Hash[1][*starter] = 1;
    long long int lstsum = 0;
    long long int penalty = 1;
    for (int j = 1; j <= min(remaining_cards, f_len3 - 5); ++j){
//        printf("seven:%d %d %d %d from %llu ",p,nw,j,k,f[p][nw][j][k]);
//        f[p][nw][j][k] += lstsum * (remaining_cards - j + 1) / penalty;
//        printf("to %llu\n",f[p][nw][j][k]);
        int nw2 = j & 1;
        Hash[nw2 ^ 1].clear();
        //debug
        long long int tsum = 0;
        for (const auto thisvec : Hash[nw2]) {
            tsum += thisvec.second;
        }
        long long int tsum2 = 1;
        for (int l = 1; l < j; ++l) {
            tsum2 *= remaining_cards - (l - 1);
        }
//        printf("%lld %lld %lld %lld\n",tsum,tsum2,tsum2 - tsum, lstsum);
        assert(tsum2 - tsum == lstsum);
        lstsum *= remaining_cards - j + 1;
        //-debug
        for (const auto thisvec : Hash[nw2]) {
            if(thisvec.second == 0) continue;
            //debug
            long long int ttst = 0;
            long long int ts = 0;
            for (int i = 0; i < 5; ++i) ts += thisvec.first[i] * i;
            for (int i = 0; i < 5; ++i) ts += thisvec.first[i + 5] * i;
            assert(ts == remaining_cards - (j - 1));

            int mink;
            for (int k = 0; k < 10; ++k) {
//                printf("++%d ", thisvec.first[k]);
            }
            for (mink = 0; mink < 5 && thisvec.first[mink] == 0; ++mink);
            assert(mink < 5);
            if(mink == 5) continue;
            //add a pair
            for (int i = 1; i < 5; ++i) {
                if(thisvec.first[i] == 0) continue;
                auto *newvec = new std::vector<int>();
                for (int k = 0; k < 10; ++k) newvec->push_back(thisvec.first[k]);
                (*newvec)[i] -= 1;
                (*newvec)[i + 5 - 1] += 1;

                for (int k = 0; k < 10; ++k) {
//                    printf("--%d ",(*newvec)[k]);
                }
                int mink2;
                for (mink2 = 0; mink2 < 5 && (*newvec)[mink2] == 0; ++mink2);
                if(mink2 < 5) {
                    assert((*newvec)[mink2] > 0);
                    (*newvec)[mink2] -= 1;
                    (*newvec)[mink2 + 5] += 1;
                }

                int sum = 0;
                for (int k = 0; k < 5; ++k) sum += thisvec.first[k];
                assert((sum & 1) == 1);

                if(sum <= 2){
                    f[p][nw][j][k] += i * thisvec.first[i] * thisvec.second / penalty;
                    lstsum += i * thisvec.first[i] * thisvec.second;
                    ttst += i * thisvec.first[i];
//                    printf("2:%lld, %d\n",ttst,remaining_cards- (j-1));
                } else {
                    if (Hash[nw2 ^ 1].count(*newvec) == 0)
                        Hash[nw2 ^ 1][*newvec] = i * thisvec.first[i] * thisvec.second;
                    else
                        Hash[nw2 ^ 1][*newvec] += i * thisvec.first[i] * thisvec.second;
                    ttst += i * thisvec.first[i];
//                    printf("3:%lld, %d\n",ttst,remaining_cards- (j-1));
                }
            }
            //add better hands
            for (int i = 1; i <= mink; ++i) {
                assert(thisvec.first[i + 5] >= 0);
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
//                printf("40:%lld,%d,%d",ttst,i,thisvec.first[i + 5]);
                ttst += i * thisvec.first[i + 5];
//                printf("4:%lld, %d,%d\n",ttst,remaining_cards- (j-1),i);
            }

            for (int i = mink + 1; i < 5; ++i) {
                assert(thisvec.first[i + 5] >= 0);
                if(thisvec.first[i + 5] <= 0) continue;
                auto *newvec = new std::vector<int>();
                for (int k = 0; k < 10; ++k) newvec->push_back(thisvec.first[k]);
                (*newvec)[i + 5] -= 1;
                (*newvec)[i - 1] += 1;
                (*newvec)[mink + 5] += 1;
                assert((*newvec)[mink] > 0);
                (*newvec)[mink] -= 1;

                if(Hash[nw2 ^ 1].count(*newvec) == 0){
                    Hash[nw2 ^ 1][*newvec] = thisvec.first[i + 5] * i * thisvec.second;
                } else {
                    Hash[nw2 ^ 1][*newvec] += thisvec.first[i + 5] * i * thisvec.second;
                }
                ttst += i * thisvec.first[i + 5];
//                printf("5:%lld, %d\n",ttst,remaining_cards- (j-1));
            }
//            printf("%lld, %d\n",ttst,remaining_cards- (j-1));
            assert(ttst == remaining_cards - (j - 1));
        }
        penalty *= j;
    }
}


int decide(const int *_hand_cnts, const int *known_remain_cnt, const int *dora, int round) {
    time_t start = clock();
    int hand_cnts[35];
    memcpy(hand_cnts, _hand_cnts, 35 * sizeof(int));
    int remaining_cards = 0;
    for (int i = 0; i < 34; ++i) remaining_cards += known_remain_cnt[i];

    int choice_num = 0;
    int hand_choices[34]={};
    for (int temp = 0; temp < 34; ++temp) {
        if (hand_cnts[temp] > 0) hand_choices[choice_num++] = temp;
    }

    //dp:initialize
    for (int t = 0; t < f_len3; ++t)
        for (int k = 0; k < tot; ++k)
            f[0][0][t][k] = 0;
    f[0][0][0][MAX_HU_VALUE + 1] = 1;

    //dp
    int branch_choice_num = 1;
    for (int i = 1; i <= 34; ++i) {
        int nw = i & 1;
        for (int p = 0; p <= branch_choice_num; ++p) {
            for (int t = 0; t < f_len3; ++t)
                for (int k = 0; k < MX; ++k)
                    f[p][nw][t][k] = 0;
        }
        for (int p = 0; p <= branch_choice_num; ++p) {
            for (int j = min(remaining_cards, f_len3 - 5); j >= 0; --j) {
                for (int k = 1; k < tot; ++k) {
                    if ((p == branch_choice_num && hand_choices[branch_choice_num - 1] == i - 1) ||
                        f[p][nw ^ 1][j][k] > 0) {
                        for (int t = known_remain_cnt[i - 1]; t >= 0; --t) {
                            int piece = (i > 27 ? 9 : i % 9);
                            if (p < branch_choice_num) {
                                if(dppath[k][hand_cnts[i - 1] + t][piece] < 0 || dppath[k][hand_cnts[i - 1] + t][piece] > tot)printf("error!");
                                f[p][nw][j + t][dppath[k][hand_cnts[i - 1] + t][piece]] +=
                                        f[p][nw ^ 1][j][k] * C[known_remain_cnt[i - 1]][t];
                            }
                            if (p == branch_choice_num) {
                                f[p][nw][j + t][dppath[k][hand_cnts[i - 1] - 1 + t][piece]] +=
                                        f[0][nw ^ 1][j][k] * C[known_remain_cnt[i - 1]][t];
                            }
                        }
                    }
                }
            }
        }
        if (hand_choices[branch_choice_num - 1] == i - 1) {
            ++branch_choice_num;
        }
            //-debug
        else {
            for (int j = min(remaining_cards, f_len3 - 1); j >= 0; --j) {
                for (int k = 1; k <= MAX_HU_VALUE; ++k) {
                    assert(f[branch_choice_num][nw][j][k] == 0);
                }
            }
        }
    }
    /*
    for (int p = 1; p < branch_choice_num; ++p) {
        int nw = 34 & 1;
        hand_cnts[hand_choices[p - 1]]--;
        seven(hand_cnts, known_remain_cnt, p, nw, 2);
        hand_cnts[hand_choices[p - 1]]++;
    }
    printf("seven:%lf ms\n",(double)(clock()-start)*1000/CLOCKS_PER_SEC); start=clock();
     */
    //+debug
    for (int p = 0; p < branch_choice_num; ++p) {
        fprintf(flog, "\n%3s,%d", p == 0 ? "   " : mname[hand_choices[p - 1]], p == 0 ? 0 : hand_cnts[hand_choices[p - 1]]);
        for (int j = 1; j <= MAX_HU_VALUE; ++j) {
            fprintf(flog, "\n f[%d],", j);
            for (int i = 1; i <= f_len3 - 5; ++i) {
                fprintf(flog, "%llu,", f[p][34 & 1][i][j]);
            }
        }
    }
    //-debug
    //dp over

    //expectance
    double expectance[43] = {}, success[43] = {};
    int close_to_hu[43] = {};
    int close_to_hu_min = 100;
    for (int p = 1; p < branch_choice_num; ++p) {
        int card = hand_choices[p - 1];
        for (int nw = 34 & 1, i = 1; i <= f_len3 - 5; ++i) {
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
        fprintf(flog, "%d %lf %lf\n", p, expectance[p], success[p]);
    }


    //find best
    assert(choice_num == branch_choice_num - 1);

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
        /*
        for (int p = 1; p < branch_choice_num; ++p) {
            int card = hand_choices[p - 1];
            int card_cnt = 4 - (known_remain_cnt[card] + hand_cnts[card]);//cards on table
            if (expectance[p] >= max_exp - 0.005 && card_cnt > max_card_cnt) {
                printf("%3s %lf %d safer than %3s %lf %d\n", mname[card], expectance[p], card_cnt, mname[best_card],
                       max_exp, max_card_cnt);
                max_exp = expectance[p] + 0.005, best_card = card, suc = success[p], max_card_cnt = card_cnt, maxp = p;
            }
        }*/
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
    /*
    if(round >= 8 && suc < 0.01){
        printf("safe: ");
        int min_cnt = 5, hand_cnt = 0;
        for (int p = 1; p < branch_choice_num; ++p) {
            int card = hand_choices[p - 1];
            int cnt = hand_cnts[card] + known_remain_cnt[card];
            if(cnt < min_cnt || (cnt == min_cnt && hand_cnts[card] >= hand_cnt)) min_cnt = cnt, real_best_card = card, hand_cnt = hand_cnts[card];
        }
    }*/
    int choice = real_best_card;
    fprintf(fout,"%d",choice);
    fprintf(flog,"%d ,",choice);
    fprintf(flog, "%3s\n", mname[choice]);
    printf("%3s\n", mname[choice]);
    int b_close_to_hu = 100;
    for (int p = 1; p < branch_choice_num; ++p) {
        int card = hand_choices[p - 1];
        b_close_to_hu = min(b_close_to_hu, close_to_hu[card]);
    }
    return b_close_to_hu;
}
int main() {
    clock_t start = clock();

    fact[0] = 1;
    for (int i = 1; i <= 136; ++i) fact[i] = fact[i - 1] * i;

    FILE* fdp = fopen("automation0.txt", "r");
    fscanf(fdp,"%d",&tot);
    for(int i = 1; i <= tot; ++i){
        for (int ci = 0; ci < 5; ++ci) {
            for (int cj = 0; cj < CHILD_NUM; ++cj) {
                fscanf(fdp, "%d", &dppath[i][ci][cj]);
            }
        }
    }
    fclose(fdp);

    fin = fopen("input.txt", "r");
    fout = fopen("output.txt", "w");
    flog = fopen("log.csv", "a");

    time_t rawtime;
    struct tm * timeinfo;
    time ( &rawtime );
    timeinfo = localtime ( &rawtime );
    fprintf(flog,"%s,\n", asctime (timeinfo) );

    int rest_num; fscanf(fin,"%d", &rest_num);
    int hand_cnt[35]; for (int i = 0; i < 34; ++ i) fscanf(fin, "%d", &hand_cnt[i]); hand_cnt[34]=0;
    int known_remain_cnt[34]; for (int i = 0; i < 34; ++ i) fscanf(fin,"%d", &known_remain_cnt[i]);
    int dora[34]; for (int i = 0; i < 34; ++ i) fscanf(fin,"%d", &dora[i]);
    fclose(fin);
    fprintf(flog,"%d,\n", rest_num);

    for (int i = 0; i < 34; ++ i){fprintf(flog, "%3s, ", mname[i]);}
    fprintf(flog, "\n");
    for (int i = 0; i < 34; ++ i) fprintf(flog, "%d, ", hand_cnt[i]);
    fprintf(flog, "\n");
    for (int i = 0; i < 34; ++ i) fprintf(flog,"%d, ", known_remain_cnt[i]);
    fprintf(flog, "\n");
    for (int i = 0; i < 34; ++ i) fprintf(flog,"%d, ", dora[i]);
    fprintf(flog, "\n");
    for (int i = 0; i < 34; ++i) {
        for (int j = 0; j < hand_cnt[i]; ++j) {
            fprintf(flog, "%3s, ", mname[i]);
            printf("%3s, ", mname[i]);
        }
    }
    fprintf(flog,"\n");
    printf("\n");

    printf("wall: ");
    for (int i = 0; i < 34; ++ i){if(known_remain_cnt[i] == 0) printf("%3s, ", mname[i]);}
    printf("\nchance: ");
    for (int i = 0; i < 34; ++ i){if(known_remain_cnt[i] == 1) printf("%3s, ", mname[i]);}
    printf("\n");

    int round = 18 - rest_num / 4;//start with 69 -> 1.end with 0 - 18.
    int b_close_to_hu = decide(hand_cnt, known_remain_cnt,dora,round);
    fclose(fout);
    fclose(flog);

    return b_close_to_hu;
}
