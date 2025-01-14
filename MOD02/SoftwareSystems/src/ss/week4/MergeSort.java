package ss.week4;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import ss.hotel.password.Checker;

public class MergeSort {
    //@ requires data != null;
	/*@
		ensures (\forall int i;
			i >= 0 && i < data.size() - 1;
			data.get(i).compareTo(data.get(i + 1)) <= 0);
	*/
    // This is an alternative option for the postcondition above.
	/*@
		ensures (\forall int i,j;
		i >= 0 && i < data.size() && j >= 0 && j < data.size();
		i <= j ==> data.get(i).compareTo(data.get(j)) <= 0);
	*/
    //@ ensures (\max int i; 0 <= i && i < data.size();
    // 		data.get(i)) == \result.get(data.size() - 1)
    //@ ensures (\min int i; 0 <= i && i < data.size();
    // 		data.get(i)) == \result.get(0)
    public static <E extends Comparable<E>> List<E> mergeSort(List<E> data) {
        if (data.size() < 2) {
            return data;
        } else {
            List<E> fst = mergeSort(data.subList(0, data.size()/2));
//			System.out.println(fst);
            List<E> snd = mergeSort(data.subList(data.size()/2, data.size()));
            List<E> res = new ArrayList<>();
            int fi = 0, si = 0;
            while (fi < fst.size() && si < snd.size()) {
                if (fst.get(fi).compareTo(snd.get(si)) <= 0) {
                    res.add(fst.get(fi));
                    fi++;
                } else {
                    res.add(snd.get(si));
                    si++;
                }
            }
            if (fi < fst.size()) {
                res.addAll(fst.subList(fi, fst.size()));
            }
            if (si < snd.size()) {
                res.addAll(snd.subList(si, snd.size()));
            }
            return res;
        }

    }

    public static void main(String[] args) {
        List<Integer> list = new ArrayList<>(Arrays.asList(9, 7 , 4 , 0 , 34, -66, 101));
		System.out.println(list);
        System.out.println(mergeSort(list));

    }

}
