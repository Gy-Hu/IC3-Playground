#include "Stats.h"
#include "boost/format.hpp"

namespace avy
{
  std::map<std::string,unsigned> Stats::counters;
  std::map<std::string,Stopwatch> Stats::sw;
  std::map<std::string,Averager> Stats::av;
  std::map<std::string,std::string> Stats::txt;

  void Stats::count (const std::string &name) { ++counters[name]; }
  double Stats::avg (const std::string &n, double v) { return av[n].add (v); }
  unsigned Stats::uset (const std::string &n, unsigned v) 
  { return counters [n] = v; }
  void Stats::set (const std::string &k, const std::string &v) { txt[k] = v; }
  unsigned Stats::get (const std::string &n) { return counters [n]; }
  

  

  void Stats::start (const std::string &name) { sw[name].start (); }
  void Stats::stop (const std::string &name) { sw[name].stop (); }
  void Stats::resume (const std::string &name) { sw[name].resume (); }
  
  /** Outputs all statistics to std output */
  void Stats::Print (std::ostream &OS)
  {
    typedef std::pair<std::string,unsigned> supair_t;
    foreach (supair_t kv, counters)
      OS << kv.first << ": " << kv.second << "\n";

    typedef std::pair<std::string,Stopwatch> sspair_t;
    foreach (sspair_t kv, sw)
      OS << kv.first << ": " << kv.second << "\n";

    typedef std::pair<std::string,Averager> avpair_t;
    foreach (avpair_t kv, av)
      OS << kv.first << ": " << kv.second << "\n";
    
    typedef std::map<std::string,std::string>::value_type txt_vt;
    foreach (txt_vt &kv, txt)
      OS << kv.first << " " << kv.second << "\n";
  }    

  void Stats::PrintBrunch (std::ostream &OS)
  {
    OS << "\n\n************** BRUNCH STATS ***************** \n";
    typedef std::pair<std::string,unsigned> supair_t;
    foreach (supair_t kv, counters)
      OS << "BRUNCH_STAT " << kv.first << " " << kv.second << "\n";

    typedef std::pair<std::string,Stopwatch> sspair_t;
    foreach (sspair_t kv, sw)
      OS << "BRUNCH_STAT " << kv.first << " " 
	 << (boost::format ("%.2f") %  (kv.second).toSeconds()) << "\n";

    typedef std::pair<std::string,Averager> avpair_t;
    foreach (avpair_t kv, av)
      OS << "BRUNCH_STAT " << kv.first << " " << kv.second << "\n";

    typedef std::map<std::string,std::string>::value_type txt_vt;
    foreach (txt_vt &kv, txt)
      OS << "BRUNCH_STAT " << kv.first << " " << kv.second << "\n";

    OS << "************** BRUNCH STATS END ***************** \n";
  }

  void Averager::Print (std::ostream &out) const
  { out << boost::format ("%.2f") << avg; }
  
}

  


