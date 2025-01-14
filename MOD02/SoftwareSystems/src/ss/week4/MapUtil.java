package ss.week4;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class MapUtil {
    //@ requires map != null;
    //@ ensures \result == true ==> map.values().size() == Set.copyOf(map.values()).size();
    public static <K, V> boolean isOneOnOne(Map<K, V> map) {
        return map.values().size() == Set.copyOf(map.values()).size();
    }
    //@ requires map!=null && range!=null;
    //@ ensures \result == false <==> (\forall V v;range.contains(v) && !map.containsValue(v));
    public static <K, V> boolean isSurjectiveOnRange(Map<K, V> map, Set<V> range) {
        for (V v : range){
            if (!map.containsValue(v)){
                return false;
            };
        }
         return true;
    }
    //@requires map!= null;
    //@ensures (\forall K key; \result.keySet().contains(map.get(key)));
    public static <K, V> Map<V, Set<K>> inverse(Map<K, V> map) {
        Map <V, Set<K>>newMap = new HashMap<>();
        Set<K> keys;
        for (K key: map.keySet()){
            if (newMap.get(map.get(key)) == null){
                keys = new HashSet<>();
            } else {
                keys = newMap.get(map.get(key));
            };
            keys.add(key);
            newMap.put(map.get(key), keys);
        }
        return newMap;
    }
    //@ requires map != null;
    //@ ensures map == inverseBijection(inverseBijection(map));
    public static <K, V> Map<V, K> inverseBijection(Map<K, V> map) {
        Map <V, K>newMap = new HashMap<>();
        for (K key: map.keySet()){
            newMap.put(map.get(key), key);
        }
        return newMap;
    }
    //@ requires f!=null && g!=null;
    //@ ensures \result == false <==> (\forall V v;f.containsValue(v) && !g.containsValue(v));
    public static <K, V, W> boolean compatible(Map<K, V> f, Map<V, W> g) {
        for (V v : f.values()) {
            if (!g.containsKey(v)) {
                return false;
            }
        }
        return true;
    }
    //@ requires f!=null && g!=null;
    //@ requires compatible(f, g);
    public static <K, V, W> Map<K, W> compose(Map<K, V> f, Map<V, W> g) {
        Map<K,W> composedMap = new HashMap<>();
        for(K key: f.keySet()){
            composedMap.put(key, g.get(f.get(key)));
        }
        return composedMap;
    }
}
